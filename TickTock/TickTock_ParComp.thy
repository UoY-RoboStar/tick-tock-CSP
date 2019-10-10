theory TickTock_ParComp
  imports TickTock_Basic_Ops TickTock_IntChoice
begin

subsection {* Parallel Composition *}

function merge_traces :: "'e ttobs list \<Rightarrow> 'e set \<Rightarrow> 'e ttobs list \<Rightarrow> 'e ttobs list set" (infixl "\<lbrakk>_\<rbrakk>\<^sup>T\<^sub>C" 55) where
  "merge_traces [] Z [] = {[]}" | 
  "merge_traces [] Z [[Y]\<^sub>R] = {[]}" | (* if one side lacks a refusal, the composition lacks a refusal *) 
  "merge_traces [] Z [[Tick]\<^sub>E] = {[]}" | (* both must terminate together *)
  "merge_traces [] Z ([Event f]\<^sub>E # \<sigma>) = {t. f \<notin> Z \<and> (\<exists> s. s \<in> merge_traces [] Z \<sigma> \<and> t = [Event f]\<^sub>E # s) \<or> f \<in> Z \<and> t = []}" | (* the event from one side is performed *) 
  "merge_traces [] Z ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = {[]}" | (* Tock must always synchronise *)
  "merge_traces [[X]\<^sub>R] Z [] = {[]}" | (* if one side lacks a refusal, the composition lacks a refusal *) 
  "merge_traces [[X]\<^sub>R] Z [[Y]\<^sub>R] = {t. \<exists> W. W \<subseteq> X \<union> Y \<and> {e. e \<in> Y \<and> e \<notin> ((Event ` Z) \<union> {Tock, Tick})} = {e. e \<in> X \<and> e \<notin> ((Event ` Z) \<union> {Tock, Tick})} \<and> t = [[W]\<^sub>R]}" | (* intersect the refusals for non-synchronised events, union for synchronised events *) 
  "merge_traces [[X]\<^sub>R] Z [[Tick]\<^sub>E] = {t. \<exists> A. A \<subseteq> Z \<and> t = [[X \<union> Event ` A]\<^sub>R]}" | (* treat Tick as refusing everything but Tock *) 
  "merge_traces [[X]\<^sub>R] Z ([Event f]\<^sub>E # \<sigma>) = {t. f \<notin> Z \<and> (\<exists> s. s \<in> merge_traces [[X]\<^sub>R] Z \<sigma> \<and> t = [Event f]\<^sub>E # s) \<or> f \<in> Z \<and> t = []}" | (* the event from one side is performed *)  
  "merge_traces [[X]\<^sub>R] Z ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = {[]}" | (* Tock must always synchronise*)  
  "merge_traces [[Tick]\<^sub>E] Z [] = {[]}" | (* both must terminate together *)
  "merge_traces [[Tick]\<^sub>E] Z [[Y]\<^sub>R] = {t. \<exists> A. A \<subseteq> Z \<and> t = [[Y \<union> Event ` A]\<^sub>R]}" | (* treat Tick as refusing everything but Tock *)
  "merge_traces [[Tick]\<^sub>E] Z [[Tick]\<^sub>E] = {[[Tick]\<^sub>E]}" | (* both terminate together *)
  "merge_traces [[Tick]\<^sub>E] Z ([Event f]\<^sub>E # \<sigma>) = {t. f \<notin> Z \<and> (\<exists> s. s \<in> merge_traces [[Tick]\<^sub>E] Z \<sigma> \<and> t = [Event f]\<^sub>E # s) \<or> f \<in> Z \<and> t = []}" | (* the event from one side is performed *) 
  "merge_traces [[Tick]\<^sub>E] Z ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = {t. (\<exists> W s. [[W]\<^sub>R] \<in> merge_traces [[Tick]\<^sub>E] Z [[Y]\<^sub>R] \<and> s \<in> merge_traces [[Tick]\<^sub>E] Z \<sigma> \<and> t = [W]\<^sub>R # [Tock]\<^sub>E # s)}" | (* Tock must synchronize, but there are implicit tocks allowed after termination, the refusal set after Tick is everything *)
  "merge_traces ([Event e]\<^sub>E # \<sigma>) Z [] = {t. e \<notin> Z \<and> (\<exists> s. s \<in> merge_traces \<sigma> Z [] \<and> t = [Event e]\<^sub>E # s) \<or> e \<in> Z \<and> t = []}" | (* the event from one side is performed *)
  "merge_traces ([Event e]\<^sub>E # \<sigma>) Z [[Y]\<^sub>R] = {t. e \<notin> Z \<and> (\<exists> s. s \<in> merge_traces \<sigma> Z [[Y]\<^sub>R] \<and> t = [Event e]\<^sub>E # s) \<or> e \<in> Z \<and> t = []}" | (* *) 
  "merge_traces ([Event e]\<^sub>E # \<sigma>) Z [[Tick]\<^sub>E] = {t. e \<notin> Z \<and> (\<exists> s. s \<in> merge_traces \<sigma> Z [[Tick]\<^sub>E] \<and> t = [Event e]\<^sub>E # s) \<or> e \<in> Z \<and> t = []}" | (* *)  
  "merge_traces ([Event e]\<^sub>E # \<rho>) Z ([Event f]\<^sub>E # \<sigma>) = 
    {t. (e \<notin> Z \<and> f \<notin> Z \<and> ((\<exists> s. s \<in> merge_traces ([Event e]\<^sub>E # \<rho>) Z \<sigma> \<and> t = [Event f]\<^sub>E # s) \<or> (\<exists> s. s \<in> merge_traces \<rho> Z ([Event f]\<^sub>E # \<sigma>) \<and> t = [Event e]\<^sub>E # s)))
      \<or> (e \<in> Z \<and> f \<notin> Z \<and> (\<exists> s. s \<in> merge_traces ([Event e]\<^sub>E # \<rho>) Z \<sigma> \<and> t = [Event f]\<^sub>E # s))
      \<or> (e \<notin> Z \<and> f \<in> Z \<and> (\<exists> s. s \<in> merge_traces \<rho> Z ([Event f]\<^sub>E # \<sigma>) \<and> t = [Event e]\<^sub>E # s))
      \<or> (e \<in> Z \<and> f \<in> Z \<and> e = f \<and> (\<exists> s. s \<in> merge_traces \<rho> Z \<sigma> \<and> t = [Event e]\<^sub>E # s))
      \<or> (e \<in> Z \<and> f \<in> Z \<and> e \<noteq> f \<and> t = [])}" | (* *) 
  "merge_traces ([Event e]\<^sub>E # \<rho>) Z ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = {t. e \<notin> Z \<and> (\<exists> s. s \<in> merge_traces \<rho> Z ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) \<and> t = [Event e]\<^sub>E # s) \<or> e \<in> Z \<and> t = []}" | (* *)  
  "merge_traces ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) Z [] = {[]}" | (* Tock must always synchronise*) 
  "merge_traces ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) Z [[Y]\<^sub>R] = {[]}" | (* Tock must always synchronise*)  
  "merge_traces ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) Z [[Tick]\<^sub>E] = {t. (\<exists> W s. [[W]\<^sub>R] \<in> merge_traces [[X]\<^sub>R] Z [[Tick]\<^sub>E] \<and> s \<in> merge_traces \<sigma> Z [[Tick]\<^sub>E] \<and> t = [W]\<^sub>R # [Tock]\<^sub>E # s)}" | (* Tock must synchronize, but there are implicit tocks allowed after termination, the refusal set after Tick is everything *)
  "merge_traces ([X]\<^sub>R # [Tock]\<^sub>E # \<rho>) Z ([Event f]\<^sub>E # \<sigma>) = {t. f \<notin> Z \<and> (\<exists> s. s \<in> merge_traces ([X]\<^sub>R # [Tock]\<^sub>E # \<rho>) Z \<sigma> \<and> t = [Event f]\<^sub>E # s) \<or> f \<in> Z \<and> t = []}" | (* *)  
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

lemma merge_traces_wf: "ttWF x \<Longrightarrow> ttWF y \<Longrightarrow> \<forall> z\<in>(x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y). ttWF z"
proof (auto, induct x A y rule:merge_traces.induct, simp+, (safe, simp+), (safe, simp+), (safe, simp+), (safe, simp), simp)
  fix Z Y \<sigma> z
  assume assm1: "\<And>x xa xb z. ttWF [[Tick]\<^sub>E] \<Longrightarrow> ttWF \<sigma> \<Longrightarrow> z \<in> [[Tick]\<^sub>E] \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C \<sigma> \<Longrightarrow> ttWF z"
  assume assm2: "ttWF ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>)"
  assume assm3: "ttWF [[Tick]\<^sub>E]"
  have \<sigma>_wf: "ttWF \<sigma>"
    using assm2 by auto
  assume "z \<in> [[Tick]\<^sub>E] \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>"
  then obtain W s where s_assms: "s \<in> [[Tick]\<^sub>E] \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C \<sigma>" "z = [W]\<^sub>R # [Tock]\<^sub>E # s"
    by auto
  then have "ttWF s"
    using assm1 \<sigma>_wf assm3 by auto
  then show "ttWF z"
    using s_assms by auto
next
  fix e \<sigma> Z z
  assume assm1: "\<And>x xa z. ttWF \<sigma> \<Longrightarrow> ttWF [] \<Longrightarrow> z \<in> \<sigma> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [] \<Longrightarrow> ttWF z"
  assume assm2: "ttWF ([Event e]\<^sub>E # \<sigma>)"
  assume assm3: "z \<in> [Event e]\<^sub>E # \<sigma> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C []"
  then obtain s where "s \<in> (\<sigma> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C []) \<and> z = [Event e]\<^sub>E # s \<or> z = []"
    by auto
  also have "ttWF \<sigma>"
    using assm2 by auto
  then show "ttWF z"
    using assm1 calculation by auto
next
  fix e \<sigma> Z Y z
  assume assm1: "\<And>x xa z. ttWF \<sigma> \<Longrightarrow> ttWF [[Y]\<^sub>R] \<Longrightarrow> z \<in> \<sigma> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [[Y]\<^sub>R] \<Longrightarrow> ttWF z"
  assume assm2: "ttWF ([Event e]\<^sub>E # \<sigma>)"
  assume assm3: "z \<in> [Event e]\<^sub>E # \<sigma> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [[Y]\<^sub>R]"
  then obtain s where "s \<in> (\<sigma> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [[Y]\<^sub>R]) \<and> z = [Event e]\<^sub>E # s \<or> z = []"
    by auto
  also have "ttWF \<sigma>"
    using assm2 by auto
  then show "ttWF z"
    using assm1 calculation by auto
next
  fix e \<sigma> Z z
  assume assm1: "\<And>x xa z. ttWF \<sigma> \<Longrightarrow> ttWF [[Tick]\<^sub>E] \<Longrightarrow> z \<in> \<sigma> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E] \<Longrightarrow> ttWF z"
  assume assm2: "ttWF ([Event e]\<^sub>E # \<sigma>)"
  assume assm3: "z \<in> [Event e]\<^sub>E # \<sigma> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
  then obtain s where "s \<in> (\<sigma> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]) \<and> z = [Event e]\<^sub>E # s \<or> z = []"
    by auto
  also have "ttWF \<sigma>"
    using assm2 by auto
  then show "ttWF z"
    using assm1 calculation by auto
next
  fix e Z f
  fix \<rho> \<sigma> z :: "'a ttobs list"
  assume assm1: "ttWF ([Event e]\<^sub>E # \<rho>)"
  assume assm2: "ttWF ([Event f]\<^sub>E # \<sigma>)"
  assume assm3: "\<And>x xa z. ttWF ([Event e]\<^sub>E # \<rho>) \<Longrightarrow> ttWF \<sigma> \<Longrightarrow> z \<in> [Event e]\<^sub>E # \<rho> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C \<sigma> \<Longrightarrow> ttWF z"
  assume assm4: "\<And>x xa z. ttWF \<rho> \<Longrightarrow> ttWF ([Event f]\<^sub>E # \<sigma>) \<Longrightarrow> z \<in> \<rho> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [Event f]\<^sub>E # \<sigma> \<Longrightarrow> ttWF z"
  assume assm5: "\<And>x xa z. ttWF \<rho> \<Longrightarrow> ttWF \<sigma> \<Longrightarrow> z \<in> \<rho> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C \<sigma> \<Longrightarrow> ttWF z"
  assume "z \<in> [Event e]\<^sub>E # \<rho> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [Event f]\<^sub>E # \<sigma>"
  then obtain s where s_assms: "z = [Event f]\<^sub>E # s \<or> z = [Event e]\<^sub>E # s \<or> z = []"
    "s \<in> ([Event e]\<^sub>E # \<rho> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C \<sigma>) \<or> s \<in> (\<rho> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [Event f]\<^sub>E # \<sigma>) \<or> s \<in> (\<rho> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C \<sigma>) \<or> z = []"
    by auto
  have \<rho>_wf: "ttWF \<rho>"
    using assm1 by auto
  have \<sigma>_wf: "ttWF \<sigma>"
    using assm2 by auto
  have "ttWF s \<or> z = []"
    using s_assms assm1 assm2 assm3 assm4 assm5 \<rho>_wf \<sigma>_wf by auto
  then show "ttWF z"
    using s_assms by auto
next
  fix e Z Y 
  fix \<rho> \<sigma> z :: "'a ttobs list"
  assume assm1: "ttWF ([Event e]\<^sub>E # \<rho>)"
  then have \<rho>_wf: "ttWF \<rho>"
    by auto
  assume assm2: "ttWF ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>)"
  assume assm3: "\<And>x xa z. ttWF \<rho> \<Longrightarrow> ttWF ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) \<Longrightarrow> z \<in> \<rho> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [Y]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<Longrightarrow> ttWF z"
  assume "z \<in> [Event e]\<^sub>E # \<rho> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>"
  then obtain s where "(s \<in> (\<rho> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) \<and> z = [Event e]\<^sub>E # s) \<or> z = []"
    by auto
  then show "ttWF z"
    using \<rho>_wf assm2 assm3 by auto
next
  fix X \<sigma> Z z
  show "z \<in> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [] \<Longrightarrow> ttWF z"
    by auto
next
  fix X \<sigma> Z Y z
  show "z \<in> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [[Y]\<^sub>R] \<Longrightarrow> ttWF z"
    by auto
next
  fix X \<sigma> Z z
  assume assm1: "ttWF ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>)"
  then have \<sigma>_wf: "ttWF \<sigma>"
    by auto
  assume assm2: "\<And>x xa xb z. ttWF \<sigma> \<Longrightarrow> ttWF [[Tick]\<^sub>E] \<Longrightarrow> z \<in> \<sigma> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E] \<Longrightarrow> ttWF z"
  assume "z \<in> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
  then obtain s W where "s \<in> \<sigma> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" "z = [W]\<^sub>R # [Tock]\<^sub>E # s"
    by auto
  then show "ttWF z"
    using \<sigma>_wf assm2 by auto
next
  fix X Z f
  fix \<rho> \<sigma> z :: "'a ttobs list"
  assume assm1: "ttWF ([Event f]\<^sub>E # \<sigma>)"
  then have \<sigma>_wf: "ttWF \<sigma>"
    by auto
  assume assm2: "ttWF ([X]\<^sub>R # [Tock]\<^sub>E # \<rho>)"
  assume assm3: "\<And>x xa z. ttWF ([X]\<^sub>R # [Tock]\<^sub>E # \<rho>) \<Longrightarrow> ttWF \<sigma> \<Longrightarrow> z \<in> [X]\<^sub>R # [Tock]\<^sub>E # \<rho> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C \<sigma> \<Longrightarrow> ttWF z"
  assume "z \<in> [X]\<^sub>R # [Tock]\<^sub>E # \<rho> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [Event f]\<^sub>E # \<sigma>"
  then obtain s where "(s \<in> ([X]\<^sub>R # [Tock]\<^sub>E # \<rho> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C \<sigma>) \<and> z = [Event f]\<^sub>E # s) \<or> z = []"
    by auto
  then show "ttWF z"
    using \<sigma>_wf assm2 assm3 by auto
next
  fix X Z Y
  fix \<rho> \<sigma> z :: "'a ttobs list"
  assume assm1: "ttWF ([X]\<^sub>R # [Tock]\<^sub>E # \<rho>)"
  then have \<rho>_wf: "ttWF \<rho>"
    by auto
  assume assm2: "ttWF ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>)"
  then have \<sigma>_wf: "ttWF \<sigma>"
    by auto
  assume assm3: "\<And>x xa xb z. ttWF \<rho> \<Longrightarrow> ttWF \<sigma> \<Longrightarrow> z \<in> \<rho> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C \<sigma> \<Longrightarrow> ttWF z"
  assume "z \<in> [X]\<^sub>R # [Tock]\<^sub>E # \<rho> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>"
  then obtain s W where "s \<in> \<rho> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C \<sigma>" "z = [W]\<^sub>R # [Tock]\<^sub>E # s"
    by auto
  then show "ttWF z"
    using \<rho>_wf \<sigma>_wf assm3 by auto
next
  fix X \<rho> Z \<sigma> z
  show "ttWF ([X]\<^sub>R # [Tick]\<^sub>E # \<rho>) \<Longrightarrow> ttWF z"
    by auto
next
  fix X e \<rho> Z \<sigma> z
  show "ttWF ([X]\<^sub>R # [Event e]\<^sub>E # \<rho>) \<Longrightarrow> ttWF z"
    by auto
next
  fix X Y \<rho> Z \<sigma> z
  show "ttWF ([X]\<^sub>R # [Y]\<^sub>R # \<rho>) \<Longrightarrow> ttWF z"
    by auto
next
  fix \<rho> Z X \<sigma> z
  show "ttWF ([X]\<^sub>R # [Tick]\<^sub>E # \<sigma>) \<Longrightarrow> ttWF z"
    by auto
next
  fix \<rho> Z X e \<sigma> z
  show "ttWF ([X]\<^sub>R # [Event e]\<^sub>E # \<sigma>) \<Longrightarrow> ttWF z"
    by auto
next
  fix \<rho> Z X Y \<sigma> z
  show "ttWF ([X]\<^sub>R # [Y]\<^sub>R # \<sigma>) \<Longrightarrow> ttWF z"
    by auto
next
  fix x \<rho> Z \<sigma> z
  show "ttWF ([Tick]\<^sub>E # x # \<rho>) \<Longrightarrow> ttWF z"
    by auto
next
  fix \<rho> Z y \<sigma> z
  show "ttWF ([Tick]\<^sub>E # y # \<sigma>) \<Longrightarrow> ttWF z"
    by auto
next
  fix \<rho> Z \<sigma> z
  show "ttWF ([Tock]\<^sub>E # \<rho>) \<Longrightarrow> ttWF z"
    by auto
next
  fix \<rho> Z \<sigma> z
  show "ttWF ([Tock]\<^sub>E # \<sigma>) \<Longrightarrow> ttWF z"
    by auto
next
  fix X Z Y \<sigma> z
  show "z \<in> [[X]\<^sub>R] \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [Y]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<Longrightarrow> ttWF z"
    by auto
next
  fix Z z
  show "z \<in> [[Tick]\<^sub>E] \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [] \<Longrightarrow> ttWF z"
    by auto
next
  fix Z Y z
  show "z \<in> [[Tick]\<^sub>E] \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [[Y]\<^sub>R] \<Longrightarrow> ttWF z"
    by auto
next
  fix Z z
  show "z \<in> [[Tick]\<^sub>E] \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E] \<Longrightarrow> ttWF z"
    by auto
next
  fix Z f \<sigma> z
  assume case_assms: "ttWF [[Tick]\<^sub>E]" "ttWF ([Event f]\<^sub>E # \<sigma>)" "z \<in> [[Tick]\<^sub>E] \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [Event f]\<^sub>E # \<sigma>"
  assume ind_hyp: "\<And>x xa z. ttWF [[Tick]\<^sub>E] \<Longrightarrow> ttWF \<sigma> \<Longrightarrow> z \<in> [[Tick]\<^sub>E] \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C \<sigma> \<Longrightarrow> ttWF z"
  show "z \<in> [[Tick]\<^sub>E] \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [Event f]\<^sub>E # \<sigma> \<Longrightarrow> ttWF z"
    using case_assms(2) ind_hyp by (cases "f \<in> Z", auto)
qed

lemma merge_traces_left_empty_tt_prefix_subset: "x \<in> merge_traces [] A q \<Longrightarrow> x \<lesssim>\<^sub>C q"
proof -
  have "\<And> x. x \<in> merge_traces [] A q \<Longrightarrow> x \<lesssim>\<^sub>C q"
    by(induct q rule:ttWF.induct, auto)
  then show "x \<in> [] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> x \<lesssim>\<^sub>C q"
    by auto
qed

lemma merge_traces_right_empty_tt_prefix_subset: "x \<in> merge_traces p A [] \<Longrightarrow> x \<lesssim>\<^sub>C p"
proof -
  have "\<And> x. x \<in> merge_traces p A [] \<Longrightarrow> x \<lesssim>\<^sub>C p"
    by (induct p rule:ttWF.induct, auto)
  then show "x \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [] \<Longrightarrow> x \<lesssim>\<^sub>C p"
    by auto
qed

definition ParCompTT :: "'e ttobs list set \<Rightarrow> 'e set \<Rightarrow> 'e ttobs list set \<Rightarrow> 'e ttobs list set" (infix "\<lbrakk>_\<rbrakk>\<^sub>C" 55) where
  "ParCompTT P A Q = \<Union> {t. \<exists> p \<in> P. \<exists> q \<in> Q. t = merge_traces p A q}"

lemma ParCompTT_wf: 
  assumes "\<forall>t\<in>P. ttWF t" "\<forall>t\<in>Q. ttWF t"
  shows "\<forall>t\<in>(P \<lbrakk>A\<rbrakk>\<^sub>C Q). ttWF t"
  unfolding ParCompTT_def
proof auto
  fix p q x
  assume "p \<in> P"
  then have p_wf: "ttWF p"
    using assms(1) by auto
  assume "q \<in> Q"
  then have q_wf: "ttWF q"
    using assms(2) by auto
  show "x \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> ttWF x"
    using p_wf q_wf merge_traces_wf by auto
qed

lemma TT0_ParComp:
  assumes "TT P" "TT Q"
  shows "TT0 (P \<lbrakk>A\<rbrakk>\<^sub>C Q)"
  unfolding TT0_def ParCompTT_def
proof auto
  have "[] \<in> P \<and> [] \<in> Q"
    using assms TT_empty by auto
  then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> x \<noteq> {}"
    apply (rule_tac x="{[]}" in exI, auto)
    apply (rule_tac x="[]" in bexI, auto)
    apply (rule_tac x="[]" in bexI, auto)
    done
qed

lemma merge_traces_empty_merge_traces_tick:
  "r \<in> (s \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C []) \<Longrightarrow> \<exists> t. t \<lesssim>\<^sub>C s \<and> r \<in> (t \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E])"
proof (induct r s rule:ttWF2.induct, auto)
  show "\<exists>t. t \<lesssim>\<^sub>C [] \<and> [] \<in> t \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
    by (rule_tac x="[]" in exI, auto)
next
  fix Y
  show "\<exists>t. t \<lesssim>\<^sub>C [[Y]\<^sub>R] \<and> [] \<in> t \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
    by (rule_tac x="[]" in exI, auto)
next
  show "\<exists>t. t \<lesssim>\<^sub>C [[Tick]\<^sub>E] \<and> [] \<in> t \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
    by (rule_tac x="[]" in exI, auto)
next
  fix Y \<sigma>
  show "\<exists>t. t \<lesssim>\<^sub>C [Y]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<and> [] \<in> t \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
    by (rule_tac x="[]" in exI, auto)
next
  fix \<rho> f \<sigma> t
  assume assm1: "f \<notin> A"
  assume assm2: "\<rho> \<in> t \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
  assume assm3: "t \<lesssim>\<^sub>C \<sigma>"
  show "\<exists>t. t \<lesssim>\<^sub>C [Event f]\<^sub>E # \<sigma> \<and> [Event f]\<^sub>E # \<rho> \<in> t \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
    using assm1 assm2 assm3 by (rule_tac x="[Event f]\<^sub>E # t" in exI, auto)
next
  fix X \<rho> \<sigma>
  assume "[X]\<^sub>R # [Tick]\<^sub>E # \<rho> \<in> \<sigma> \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C []"
  then show "\<exists>t. t \<lesssim>\<^sub>C \<sigma> \<and> [X]\<^sub>R # [Tick]\<^sub>E # \<rho> \<in> t \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
    by (induct \<sigma> rule:ttWF.induct, auto)
next
  fix X e \<rho> \<sigma>
  assume "[X]\<^sub>R # [Event e]\<^sub>E # \<rho> \<in> \<sigma> \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C []"
  then show "\<exists>t. t \<lesssim>\<^sub>C \<sigma> \<and> [X]\<^sub>R # [Event e]\<^sub>E # \<rho> \<in> t \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
    by (induct \<sigma> rule:ttWF.induct, auto)
next
  fix X Y \<rho> \<sigma>
  assume "[X]\<^sub>R # [Y]\<^sub>R # \<rho> \<in> \<sigma> \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C []"
  then show "\<exists>t. t \<lesssim>\<^sub>C \<sigma> \<and> [X]\<^sub>R # [Y]\<^sub>R # \<rho> \<in> t \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
    by (induct \<sigma> rule:ttWF.induct, auto)
next
  fix x \<rho> \<sigma>
  assume "[Tick]\<^sub>E # x # \<rho> \<in> \<sigma> \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C []"
  then show "\<exists>t. t \<lesssim>\<^sub>C \<sigma> \<and> [Tick]\<^sub>E # x # \<rho> \<in> t \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
    by (induct \<sigma> rule:ttWF.induct, auto)
next
  fix \<rho> \<sigma>
  assume "[Tock]\<^sub>E # \<rho> \<in> \<sigma> \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C []"
  then show "\<exists>t. t \<lesssim>\<^sub>C \<sigma> \<and> [Tock]\<^sub>E # \<rho> \<in> t \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
    by (induct \<sigma> rule:ttWF.induct, auto)
next
  fix f \<sigma>
  show "\<exists>t. t \<lesssim>\<^sub>C [Event f]\<^sub>E # \<sigma> \<and> [] \<in> t \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
    by (rule_tac x="[]" in exI, auto)
qed

lemma merge_traces_tick_merge_traces_empty:
  "r \<in> (s \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]) \<Longrightarrow> \<exists> t. t \<lesssim>\<^sub>C r \<and> t \<in> (s \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [])"
proof (induct r s rule:ttWF2.induct, auto)
  fix \<rho> f \<sigma> t
  show "t \<lesssim>\<^sub>C \<rho> \<Longrightarrow> t \<in> \<sigma> \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [] \<Longrightarrow> \<exists>t. t \<lesssim>\<^sub>C [Event f]\<^sub>E # \<rho> \<and> (\<exists>s. s \<in> (\<sigma> \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C []) \<and> t = [Event f]\<^sub>E # s)"
    by (rule_tac x="[Event f]\<^sub>E # t" in exI, auto)
next
  fix X \<rho> \<sigma>
  show "[X]\<^sub>R # [Tick]\<^sub>E # \<rho> \<in> \<sigma> \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E] \<Longrightarrow> \<exists>t. t \<lesssim>\<^sub>C [X]\<^sub>R # [Tick]\<^sub>E # \<rho> \<and> t \<in> \<sigma> \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C []"
    by (induct \<sigma> rule:ttWF.induct, auto)
next
  fix X e \<rho> \<sigma>
  show "[X]\<^sub>R # [Event e]\<^sub>E # \<rho> \<in> \<sigma> \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E] \<Longrightarrow> \<exists>t. t \<lesssim>\<^sub>C [X]\<^sub>R # [Event e]\<^sub>E # \<rho> \<and> t \<in> \<sigma> \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C []"
    by (induct \<sigma> rule:ttWF.induct, auto)
next
  fix X Y \<rho> \<sigma>
  show "[X]\<^sub>R # [Y]\<^sub>R # \<rho> \<in> \<sigma> \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E] \<Longrightarrow> \<exists>t. t \<lesssim>\<^sub>C [X]\<^sub>R # [Y]\<^sub>R # \<rho> \<and> t \<in> \<sigma> \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C []"
    by (induct \<sigma> rule:ttWF.induct, auto)
next
  fix x \<rho> \<sigma>
  show "[Tick]\<^sub>E # x # \<rho> \<in> \<sigma> \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E] \<Longrightarrow> \<exists>t. t \<lesssim>\<^sub>C [Tick]\<^sub>E # x # \<rho> \<and> t \<in> \<sigma> \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C []"
    by (induct \<sigma> rule:ttWF.induct, auto)
next
  fix \<rho> \<sigma>
  show "[Tock]\<^sub>E # \<rho> \<in> \<sigma> \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E] \<Longrightarrow> \<exists>t. t \<lesssim>\<^sub>C [Tock]\<^sub>E # \<rho> \<and> t \<in> \<sigma> \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C []"
    by (induct \<sigma> rule:ttWF.induct, auto)
qed

lemma TT1_ParComp:
  assumes "TT P" "TT Q"
  shows "TT1 (P \<lbrakk>A\<rbrakk>\<^sub>C Q)"
  unfolding TT1_def ParCompTT_def
proof (auto)
  fix \<rho> \<sigma> p q :: "'a ttobs list"
  have 1: "\<And> p q. \<rho> \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> \<exists>p'. \<exists>q'. p' \<lesssim>\<^sub>C p \<and> q' \<lesssim>\<^sub>C q \<and> \<rho> \<in> (p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
  proof (induct \<rho> \<sigma> rule:ttWF2.induct, auto)
    fix p q :: "'a ttobs list"
    have "[] \<lesssim>\<^sub>C p \<and> ([] \<lesssim>\<^sub>C q \<and> [] \<in> [] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [])"
      by auto
    then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
      by blast
  next
    fix p q :: "'a ttobs list"
    have "[] \<lesssim>\<^sub>C p \<and> ([] \<lesssim>\<^sub>C q \<and> [] \<in> [] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [])"
      by auto
    then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
      by blast
  next
    fix p q :: "'a ttobs list"
    have "[] \<lesssim>\<^sub>C p \<and> ([] \<lesssim>\<^sub>C q \<and> [] \<in> [] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [])"
      by auto
    then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
      by blast
  next
    fix p q :: "'a ttobs list"
    have "[] \<lesssim>\<^sub>C p \<and> ([] \<lesssim>\<^sub>C q \<and> [] \<in> [] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [])"
      by auto
    then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
      by blast
  next
    fix p q :: "'a ttobs list"
    have "[] \<lesssim>\<^sub>C p \<and> ([] \<lesssim>\<^sub>C q \<and> [] \<in> [] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [])"
      by auto
    then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
      by blast
  next
    fix p q :: "'a ttobs list"
    fix X Y
    assume assm1: "[[Y]\<^sub>R] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    assume assm2: "X \<subseteq> Y"
    then obtain Y1 Y2 where "Y \<subseteq> Y1 \<union> Y2 \<and> (p = [[Y1]\<^sub>R] \<and> q = [[Y2]\<^sub>R]) \<or> (p = [[Tick]\<^sub>E] \<and> q = [[Y2]\<^sub>R]) \<or> (p = [[Y1]\<^sub>R] \<and> q = [[Tick]\<^sub>E]) "
      using assm1 by (induct p A q rule:merge_traces.induct, auto)
    then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [[X]\<^sub>R] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
      using assm1 assm2 apply auto
      apply (rule_tac x="[[Y1 \<inter> X]\<^sub>R]" in exI, simp, rule_tac x="[[Y2 \<inter> X]\<^sub>R]" in exI, auto)
      apply (rule_tac x="[[Tick]\<^sub>E]" in exI, simp, rule_tac x="[[Y2 \<inter> X]\<^sub>R]" in exI, auto)
      apply (rule_tac x= "Event -` X \<inter> Aa" in exI, auto)
      apply (rule_tac x="[[Y1 \<inter> X]\<^sub>R]" in exI, simp, rule_tac x="[[Tick]\<^sub>E]" in exI, auto)
      apply (rule_tac x= "Event -` X \<inter> Aa" in exI, auto)
      done
  next
    fix p q \<sigma> :: "'a ttobs list"
    fix X Y
    assume assm1: "[Y]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    assume assm2: "X \<subseteq> Y"
    assume assm3: "\<And>p q. \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> \<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
    have "(\<exists> Y1 Y2 p' q'. p = [Y1]\<^sub>R # [Tock]\<^sub>E # p' \<and> q = [Y2]\<^sub>R # [Tock]\<^sub>E # q')
      \<or> (\<exists> Y1 Y2 p' q'. p = [[Tick]\<^sub>E] \<and> q = [Y2]\<^sub>R # [Tock]\<^sub>E # q')
      \<or> (\<exists> Y1 Y2 p' q'. p = [Y1]\<^sub>R # [Tock]\<^sub>E # p' \<and> q = [[Tick]\<^sub>E])"
      using assm1 by (induct p A q rule:merge_traces.induct, simp_all)
    then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [[X]\<^sub>R] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
    proof auto
      fix Y1 Y2 p' q' 
      assume case_assm: "p = [Y1]\<^sub>R # [Tock]\<^sub>E # p'" "q = [Y2]\<^sub>R # [Tock]\<^sub>E # q'"
      then have "X \<subseteq> Y1 \<union> Y2"
        using assm1 assm2 by auto
      then show "\<exists>p'a. p'a \<lesssim>\<^sub>C [Y1]\<^sub>R # [Tock]\<^sub>E # p' \<and> (\<exists>q'a. q'a \<lesssim>\<^sub>C [Y2]\<^sub>R # [Tock]\<^sub>E # q' \<and> [[X]\<^sub>R] \<in> p'a \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'a)"
        using assm1 case_assm by (rule_tac x="[[Y1]\<^sub>R]" in exI, simp, rule_tac x="[[Y2]\<^sub>R]" in exI, simp)
    next
      fix Y2 q'
      assume case_assm: "p = [[Tick]\<^sub>E]" "q = [Y2]\<^sub>R # [Tock]\<^sub>E # q'"
      then show "\<exists>p'a. p'a \<lesssim>\<^sub>C [[Tick]\<^sub>E] \<and> (\<exists>q'a. q'a \<lesssim>\<^sub>C [Y2]\<^sub>R # [Tock]\<^sub>E # q' \<and> [[X]\<^sub>R] \<in> p'a \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'a)"
        using assm1 assm2 case_assm
        apply (rule_tac x="[[Tick]\<^sub>E]" in exI, simp, rule_tac x="[[Y2 \<inter> X]\<^sub>R]" in exI, simp, safe)
        by (rule_tac x= "Event -` X \<inter> Aa" in exI, auto)
    next
      fix Y1 p'
      assume case_assm: "p = [Y1]\<^sub>R # [Tock]\<^sub>E # p'" "q = [[Tick]\<^sub>E]"
      then show "\<exists>p'a. p'a \<lesssim>\<^sub>C [Y1]\<^sub>R # [Tock]\<^sub>E # p' \<and> (\<exists>q'. q' \<lesssim>\<^sub>C [[Tick]\<^sub>E] \<and> [[X]\<^sub>R] \<in> p'a \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
        using assm1 assm2 case_assm
        apply (rule_tac x="[[Y1 \<inter> X]\<^sub>R]" in exI, simp, rule_tac x="[[Tick]\<^sub>E]" in exI, simp, safe)
        by (rule_tac x= "Event -` X \<inter> Aa" in exI, auto)
    qed
  next
    fix p q
    assume "[[Tick]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    then have "p = [[Tick]\<^sub>E] \<and> q = [[Tick]\<^sub>E]"
      by (induct p A q rule:merge_traces.induct, auto)
    then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [[Tick]\<^sub>E] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
      by (rule_tac x="[[Tick]\<^sub>E]" in exI, simp, rule_tac x="[[Tick]\<^sub>E]" in exI, simp)
  next
    fix \<rho> f \<sigma> p q
    assume assm1: "[Event f]\<^sub>E # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    assume assm2: "\<rho> \<lesssim>\<^sub>C \<sigma>"
    assume assm3: "\<And>p q. \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> \<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
    show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [Event f]\<^sub>E # \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
    proof (cases "f \<in> A")
      assume case_assm: "f \<in> A"
      then obtain p' q' where 1: "p = [Event f]\<^sub>E # p'" "q = [Event f]\<^sub>E # q'"
        using assm1 by (induct p A q rule:merge_traces.induct, auto)
      then obtain p'' q'' where "p'' \<lesssim>\<^sub>C p'" "q'' \<lesssim>\<^sub>C q'" "\<rho> \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q''"
        using case_assm assm1 assm3 by (auto, blast)
      then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [Event f]\<^sub>E # \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
        using 1 case_assm by (rule_tac x="[Event f]\<^sub>E # p''" in exI, simp, rule_tac x="[Event f]\<^sub>E # q''" in exI, simp)
    next
      assume case_assm: "f \<notin> A"
      then obtain p' q' Y1 Y2 e where 1: "(p = [Event f]\<^sub>E # p' \<and> q = [Event e]\<^sub>E # q' \<and> \<sigma> \<in> (p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event e]\<^sub>E # q')) 
        \<or> (p = [Event e]\<^sub>E # p' \<and> q = [Event f]\<^sub>E # q' \<and> \<sigma> \<in> ([Event e]\<^sub>E # p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'))
        \<or> (p = [] \<and> q = [Event f]\<^sub>E # q')
        \<or> (p = [Event f]\<^sub>E # p' \<and> q = [])
        \<or> (p = [[Y1]\<^sub>R] \<and> q = [Event f]\<^sub>E # q')
        \<or> (p = [Event f]\<^sub>E # p' \<and> q = [[Y2]\<^sub>R])
        \<or> (p = [Event f]\<^sub>E # p' \<and> q = [[Tick]\<^sub>E]) 
        \<or> (p = [[Tick]\<^sub>E] \<and> q = [Event f]\<^sub>E # q')
        \<or> (p = [Event f]\<^sub>E # p' \<and> q = [Y2]\<^sub>R # [Tock]\<^sub>E # q') 
        \<or> (p = [Y1]\<^sub>R # [Tock]\<^sub>E # p' \<and> q = [Event f]\<^sub>E # q')"
        using assm1 by (cases "(p, q)" rule:ttWF2.cases, auto)
      then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [Event f]\<^sub>E # \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
      proof auto
        assume case_assm2: "q = [Event e]\<^sub>E # q'" "p = [Event f]\<^sub>E # p'" "\<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event e]\<^sub>E # q'"
        then obtain p'' q'' where "p'' \<lesssim>\<^sub>C p'" "q'' \<lesssim>\<^sub>C [Event e]\<^sub>E # q'" "\<rho> \<in> (p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'')"
          using assm3 by blast
        then show "\<exists>p'a. p'a \<lesssim>\<^sub>C [Event f]\<^sub>E # p' \<and> (\<exists>q'a. q'a \<lesssim>\<^sub>C [Event e]\<^sub>E # q' \<and> [Event f]\<^sub>E # \<rho> \<in> p'a \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'a)"
          using case_assm assm1 by (rule_tac x="[Event f]\<^sub>E # p''" in exI, simp, rule_tac x="q''" in exI, cases q'' rule:ttWF.cases, auto)
      next
        assume case_assm2: "q = [Event f]\<^sub>E # q'" "p = [Event e]\<^sub>E # p'" "\<sigma> \<in> [Event e]\<^sub>E # p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'"
        then obtain p'' q'' where "p'' \<lesssim>\<^sub>C [Event e]\<^sub>E # p'" "q'' \<lesssim>\<^sub>C q'" "\<rho> \<in> (p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'')"
          using assm3 by blast
        then show "\<exists>p'a. p'a \<lesssim>\<^sub>C [Event e]\<^sub>E # p' \<and> (\<exists>q'a. q'a \<lesssim>\<^sub>C [Event f]\<^sub>E # q' \<and> [Event f]\<^sub>E # \<rho> \<in> p'a \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'a)"
          using case_assm assm1 by (rule_tac x=" p''" in exI, simp, rule_tac x="[Event f]\<^sub>E # q''" in exI, cases p'' rule:ttWF.cases, auto)
      next
        assume case_assm2: "q = [Event f]\<^sub>E # q'" "p = []"
        then have "\<sigma> \<in> [] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'"
          using assm1 by auto
        then obtain q'' where "q'' \<lesssim>\<^sub>C q'" "\<rho> \<in> ([] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'')"
          using assm3 tt_prefix_subset.simps(1) tt_prefix_subset_antisym by blast
        then show "\<exists>p'. p' \<lesssim>\<^sub>C [] \<and> (\<exists>q'a. q'a \<lesssim>\<^sub>C [Event f]\<^sub>E # q' \<and> [Event f]\<^sub>E # \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'a)"
          using case_assm assm1 by (rule_tac x="[]" in exI, simp, rule_tac x="[Event f]\<^sub>E # q''" in exI, auto)
      next
        assume case_assm2: "p = [Event f]\<^sub>E # p'" "q = []"
        then have "\<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C []"
          using assm1 by auto
        then obtain p'' where "p'' \<lesssim>\<^sub>C p'" "\<rho> \<in> (p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [])"
          using assm3 tt_prefix_subset.simps(1) tt_prefix_subset_antisym by blast
        then show "\<exists>p'a. p'a \<lesssim>\<^sub>C [Event f]\<^sub>E # p' \<and> (\<exists>q'. q' \<lesssim>\<^sub>C [] \<and> [Event f]\<^sub>E # \<rho> \<in> p'a \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
          using case_assm assm1 by (rule_tac x="[Event f]\<^sub>E # p''" in exI, simp, rule_tac x="[]" in exI, auto)
      next
        assume case_assm2: "p = [Event f]\<^sub>E # p'" "q = [[Y2]\<^sub>R]"
        then have 1: "\<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Y2]\<^sub>R]"
          using assm1 by auto
        then obtain p'' q'' where "p'' \<lesssim>\<^sub>C p'" "q'' \<lesssim>\<^sub>C [[Y2]\<^sub>R]" "\<rho> \<in> (p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'')"
          using assm3 tt_prefix_subset.simps(1) tt_prefix_subset_antisym by blast
        then show "\<exists>p'a. p'a \<lesssim>\<^sub>C [Event f]\<^sub>E # p' \<and> (\<exists>q'. q' \<lesssim>\<^sub>C [[Y2]\<^sub>R] \<and> [Event f]\<^sub>E # \<rho> \<in> p'a \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
          using case_assm assm1 by (rule_tac x="[Event f]\<^sub>E # p''" in exI, simp, rule_tac x="q''" in exI, cases q'' rule:ttWF.cases, auto)
      next
        assume case_assm2: "q = [Event f]\<^sub>E # q'" "p = [[Y1]\<^sub>R]"
        then have 1: "\<sigma> \<in> [[Y1]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'"
          using assm1 by auto
        then obtain p'' q'' where "p'' \<lesssim>\<^sub>C [[Y1]\<^sub>R]" "q'' \<lesssim>\<^sub>C q'" "\<rho> \<in> (p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'')"
          using assm3 tt_prefix_subset.simps(1) tt_prefix_subset_antisym by blast
        then show "\<exists>p'. p' \<lesssim>\<^sub>C [[Y1]\<^sub>R] \<and> (\<exists>q'a. q'a \<lesssim>\<^sub>C [Event f]\<^sub>E # q' \<and> [Event f]\<^sub>E # \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'a)"
          using case_assm assm1 by (rule_tac x="p''" in exI, simp, rule_tac x="[Event f]\<^sub>E # q''" in exI, cases p'' rule:ttWF.cases, auto)
      next
        assume case_assm2: "q = [Event f]\<^sub>E # q'" "p = [[Tick]\<^sub>E]"
        then have 1: "\<sigma> \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'"
          using assm1 by auto
        then obtain p'' q'' where "p'' \<lesssim>\<^sub>C [[Tick]\<^sub>E]" "q'' \<lesssim>\<^sub>C q'" "\<rho> \<in> (p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'')"
          using assm3 tt_prefix_subset.simps(1) tt_prefix_subset_antisym by blast
        then show "\<exists>p'. p' \<lesssim>\<^sub>C [[Tick]\<^sub>E] \<and> (\<exists>q'a. q'a \<lesssim>\<^sub>C [Event f]\<^sub>E # q' \<and> [Event f]\<^sub>E # \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'a)"
          using case_assm assm1 by (rule_tac x="p''" in exI, simp, rule_tac x="[Event f]\<^sub>E # q''" in exI, cases p'' rule:ttWF.cases, auto)
      next
        assume case_assm2: "p = [Event f]\<^sub>E # p'" "q = [[Tick]\<^sub>E]"
        then have 1: "\<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
          using assm1 by auto
        then obtain p'' q'' where "q'' \<lesssim>\<^sub>C [[Tick]\<^sub>E]" "p'' \<lesssim>\<^sub>C p'" "\<rho> \<in> (p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'')"
          using assm3 tt_prefix_subset.simps(1) tt_prefix_subset_antisym by blast
        then show "\<exists>p'a. p'a \<lesssim>\<^sub>C [Event f]\<^sub>E # p' \<and> (\<exists>q'. q' \<lesssim>\<^sub>C [[Tick]\<^sub>E] \<and> [Event f]\<^sub>E # \<rho> \<in> p'a \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
          using case_assm assm1 by (rule_tac x="[Event f]\<^sub>E # p''" in exI, simp, rule_tac x="q''" in exI, cases q'' rule:ttWF.cases, auto)
      next
        assume case_assm2: "q = [Event f]\<^sub>E # q'" "p = [Y1]\<^sub>R # [Tock]\<^sub>E # p'"
        then have 1: "\<sigma> \<in> [Y1]\<^sub>R # [Tock]\<^sub>E # p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'"
          using assm1 by auto
        then obtain p'' q'' where "p'' \<lesssim>\<^sub>C [Y1]\<^sub>R # [Tock]\<^sub>E # p'" "q'' \<lesssim>\<^sub>C q'" "\<rho> \<in> (p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'')"
          using assm3 tt_prefix_subset.simps(1) tt_prefix_subset_antisym by blast
        then show "\<exists>p'a. p'a \<lesssim>\<^sub>C [Y1]\<^sub>R # [Tock]\<^sub>E # p' \<and> (\<exists>q'a. q'a \<lesssim>\<^sub>C [Event f]\<^sub>E # q' \<and> [Event f]\<^sub>E # \<rho> \<in> p'a \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'a)"
          using case_assm assm1 by (rule_tac x="p''" in exI, simp, rule_tac x="[Event f]\<^sub>E # q''" in exI, cases p'' rule:ttWF.cases, auto)
      next
        assume case_assm2: "p = [Event f]\<^sub>E # p'" "q = [Y2]\<^sub>R # [Tock]\<^sub>E # q'"
        then have 1: "\<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Y2]\<^sub>R # [Tock]\<^sub>E # q'"
          using assm1 by auto
        then obtain p'' q'' where "q'' \<lesssim>\<^sub>C [Y2]\<^sub>R # [Tock]\<^sub>E # q'" "p'' \<lesssim>\<^sub>C p'" "\<rho> \<in> (p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'')"
          using assm3 tt_prefix_subset.simps(1) tt_prefix_subset_antisym by blast
        then show "\<exists>p'a. p'a \<lesssim>\<^sub>C [Event f]\<^sub>E # p' \<and> (\<exists>q'a. q'a \<lesssim>\<^sub>C [Y2]\<^sub>R # [Tock]\<^sub>E # q' \<and> [Event f]\<^sub>E # \<rho> \<in> p'a \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'a)"
          using case_assm assm1 by (rule_tac x="[Event f]\<^sub>E # p''" in exI, simp, rule_tac x="q''" in exI, cases q'' rule:ttWF.cases, auto)
      qed
    qed
  next
    fix X \<rho> Y \<sigma> p q
    assume assm1: "[Y]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    assume assm2: "X \<subseteq> Y"
    assume assm3: "\<rho> \<lesssim>\<^sub>C \<sigma>"
    assume assm4: "\<And>p q. \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> \<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
    obtain Y1 Y2 p' q' where "(p = [Y1]\<^sub>R # [Tock]\<^sub>E # p' \<and> q = [Y2]\<^sub>R # [Tock]\<^sub>E # q')
      \<or> (p = [Y1]\<^sub>R # [Tock]\<^sub>E # p' \<and> q = [[Tick]\<^sub>E])
      \<or> (p = [[Tick]\<^sub>E] \<and> q = [Y2]\<^sub>R # [Tock]\<^sub>E # q')"
      using assm1 by (induct p A q rule:merge_traces.induct, simp_all)
    then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
    proof auto
      assume case_assm: "q = [Y2]\<^sub>R # [Tock]\<^sub>E # q'" "p = [Y1]\<^sub>R # [Tock]\<^sub>E # p'"
      then have "\<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'"
        using assm1 by auto
      then obtain p'' q'' where "p'' \<lesssim>\<^sub>C p'" "q'' \<lesssim>\<^sub>C q'" "\<rho> \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q''"
        using assm4 by blast
      then show "\<exists>p'a. p'a \<lesssim>\<^sub>C [Y1]\<^sub>R # [Tock]\<^sub>E # p' \<and> (\<exists>q'a. q'a \<lesssim>\<^sub>C [Y2]\<^sub>R # [Tock]\<^sub>E # q' \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<rho> \<in> p'a \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'a)"
        using assm1 assm2 case_assm by (rule_tac x="[Y1]\<^sub>R # [Tock]\<^sub>E # p''" in exI, simp, rule_tac x="[Y2]\<^sub>R # [Tock]\<^sub>E # q''" in exI, auto)
    next
      assume case_assm: "q = [[Tick]\<^sub>E]" "p = [Y1]\<^sub>R # [Tock]\<^sub>E # p'"
      then have 1: "\<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
        using assm1 by auto
      then obtain p'' q'' where 1: "p'' \<lesssim>\<^sub>C p'" "q'' \<lesssim>\<^sub>C [[Tick]\<^sub>E]" "\<rho> \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q''"
        using assm4 by blast
      then have "q'' = [] \<or> q'' = [[Tick]\<^sub>E]"
        by (cases q'' rule:ttWF.cases, auto)
      then obtain p''' where "p''' \<lesssim>\<^sub>C p'" "\<rho> \<in> p''' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
        using 1 apply auto
        using tt_prefix_subset_trans merge_traces_empty_merge_traces_tick by blast
      then show "\<exists>p'a. p'a \<lesssim>\<^sub>C [Y1]\<^sub>R # [Tock]\<^sub>E # p' \<and> (\<exists>q'. q' \<lesssim>\<^sub>C [[Tick]\<^sub>E] \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<rho> \<in> p'a \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
        using assm1 assm2 case_assm
        apply (rule_tac x="[Y1 \<inter> X]\<^sub>R # [Tock]\<^sub>E # p'''" in exI, simp, rule_tac x="[[Tick]\<^sub>E]" in exI, auto)
        by (rule_tac x= "Event -` X \<inter> Aa" in exI, auto)
    next
      assume case_assm: "p = [[Tick]\<^sub>E]" "q = [Y2]\<^sub>R # [Tock]\<^sub>E # q'"
      then have 1: "\<sigma> \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'"
        using assm1 by auto
      then obtain p'' q'' where 1: "q'' \<lesssim>\<^sub>C q'" "p'' \<lesssim>\<^sub>C [[Tick]\<^sub>E]" "\<rho> \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q''"
        using assm4 by blast
      then have "p'' = [] \<or> p'' = [[Tick]\<^sub>E]"
        by (cases p'' rule:ttWF.cases, auto)
      then obtain q''' where "q''' \<lesssim>\<^sub>C q'" "\<rho> \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'''"
        using 1 apply auto
        using tt_prefix_subset_trans merge_traces_comm merge_traces_empty_merge_traces_tick by blast
      then show "\<exists>p'. p' \<lesssim>\<^sub>C [[Tick]\<^sub>E] \<and> (\<exists>q'a. q'a \<lesssim>\<^sub>C [Y2]\<^sub>R # [Tock]\<^sub>E # q' \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'a)"
        using assm1 assm2 case_assm 
        apply (rule_tac x="[[Tick]\<^sub>E]" in exI, simp, rule_tac x="[Y2 \<inter> X]\<^sub>R # [Tock]\<^sub>E # q'''" in exI, auto)
        by (rule_tac x= "Event -` X \<inter> Aa" in exI, auto)
    qed
  next
    fix X \<rho> \<sigma> p q
    show "[X]\<^sub>R # [Tick]\<^sub>E # \<rho> \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> \<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [X]\<^sub>R # [Tick]\<^sub>E # \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
      by (induct \<sigma> rule:ttWF.induct, auto, induct p q rule:ttWF2.induct, auto)
  next
    fix X e \<rho> \<sigma> p q
    show "[X]\<^sub>R # [Event e]\<^sub>E # \<rho> \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> \<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [X]\<^sub>R # [Event e]\<^sub>E # \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
      by (induct \<sigma> rule:ttWF.induct, auto, induct p q rule:ttWF2.induct, auto)
  next
    fix X Y \<rho> \<sigma> p q
    show "[X]\<^sub>R # [Y]\<^sub>R # \<rho> \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> \<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [X]\<^sub>R # [Y]\<^sub>R # \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
      by (induct \<sigma> rule:ttWF.induct, auto, induct p q rule:ttWF2.induct, auto)
  next
    fix \<rho> X \<sigma> p q
    show "[X]\<^sub>R # [Tick]\<^sub>E # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> \<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
      by (induct p q rule:ttWF2.induct, auto)
  next
    fix \<rho> X e \<sigma> p q
    show "[X]\<^sub>R # [Event e]\<^sub>E # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> \<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
      by (induct p q rule:ttWF2.induct, auto)
  next
    fix \<rho> X Y \<sigma> p q
    show "[X]\<^sub>R # [Y]\<^sub>R # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> \<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
      by (induct p q rule:ttWF2.induct, auto)
  next
    fix x \<rho> \<sigma> p q
    show "[Tick]\<^sub>E # x # \<rho> \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> \<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [Tick]\<^sub>E # x # \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
      by (cases x, auto, (induct \<sigma> rule:ttWF.induct, auto, induct p q rule:ttWF2.induct, auto, induct p q rule:ttWF2.induct, auto)+)
  next
    fix \<rho> y \<sigma> p q
    show "[Tick]\<^sub>E # y # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> \<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
      by (induct p q rule:ttWF2.induct, auto)
  next
    fix \<rho> \<sigma> p q
    show "[Tock]\<^sub>E # \<rho> \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> \<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [Tock]\<^sub>E # \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
      by (induct \<sigma> rule:ttWF.induct, auto, (induct p q rule:ttWF2.induct, auto)+)
  next
    fix \<rho> \<sigma> p q
    show "[Tock]\<^sub>E # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> \<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
      by (induct p q rule:ttWF2.induct, auto)
  qed
  assume assm1: "\<rho> \<lesssim>\<^sub>C \<sigma>"
  assume assm2: "\<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
  assume assm3: "p \<in> P"
  assume assm4: "q \<in> Q"
  obtain p' q' where 2: "p' \<lesssim>\<^sub>C p \<and> q' \<lesssim>\<^sub>C q \<and> \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'"  
    using 1 assm1 assm2 by blast
  then have "p' \<in> P \<and> q' \<in> Q"
    using TT1_def TT_TT1 assm3 assm4 assms(1) assms(2) by blast
  then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<rho> \<in> x"
    using 2 by auto
qed

lemma TT2w_ParComp:
  "\<And> P Q. TT P \<Longrightarrow> TT Q \<Longrightarrow> TT2w (P \<lbrakk>A\<rbrakk>\<^sub>C Q)"
  unfolding TT2w_def ParCompTT_def
proof (auto)
  fix \<rho>
  show "\<And>P Q X Y p q. TT P \<Longrightarrow> TT Q \<Longrightarrow>
    Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<rho> @ [[e]\<^sub>E] \<in> x) \<or>
      e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> x)} = {} \<Longrightarrow>
    \<rho> @ [[X]\<^sub>R] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> p \<in> P \<Longrightarrow> q \<in> Q \<Longrightarrow> \<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<rho> @ [[X \<union> Y]\<^sub>R] \<in> x"
  proof (induct \<rho> rule:ttWF.induct, auto)
    fix P Q :: "'a ttobs list set"
    fix X Y p q
    assume TT_P: "TT P" and TT_Q: "TT Q"
    assume p_P: "p \<in> P" and q_Q: "q \<in> Q"
    assume assm1: "Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[e]\<^sub>E] \<in> x) \<or>
      e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> x)} = {}"
    assume assm2: "[[X]\<^sub>R] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    have TT2w_P: "TT2w P"
      using TT_P unfolding TT_def by auto
    have TT2w_Q: "TT2w Q"
      using TT_Q unfolding TT_def by auto
    have p_q_cases: "(\<exists> Z W. p = [[Z]\<^sub>R] \<and> q = [[W]\<^sub>R] \<and> X \<subseteq> Z \<union> W \<and> {e \<in> Z. e \<notin> Event ` A \<union> {Tock, Tick}} = {e \<in> W. e \<notin> Event ` A \<union> {Tock, Tick}})
      \<or> (\<exists> Z B. p = [[Z]\<^sub>R] \<and> q = [[Tick]\<^sub>E] \<and> X = Z \<union> Event ` B \<and> B \<subseteq> A)
      \<or> (\<exists> W B. p = [[Tick]\<^sub>E] \<and> q = [[W]\<^sub>R] \<and> X \<subseteq> Event ` B \<union> W \<and> B \<subseteq> A)"
      using assm2 by (cases "(p, q)" rule:ttWF2.cases, auto)
    have set1: "{e. \<exists> ea. e = Event ea \<and> ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> P} \<union> {e. \<exists> ea. e = Event ea \<and> ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> Q}
      \<subseteq> {e. \<exists> ea. e = Event ea \<and> ea \<notin> A \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[Event ea]\<^sub>E] \<in> x)}"
    proof auto
      fix x
      assume "[[Event x]\<^sub>E] \<in> P" "x \<notin> A"
      also have "[] \<in> Q"
        by (simp add: TT_empty TT_Q)
      then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[Event x]\<^sub>E] \<in> xa"
        using calculation apply (rule_tac x="[[Event x]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C []" in exI, auto)
        apply (rule_tac x="[[Event x]\<^sub>E]" in bexI, auto)
        apply (rule_tac x="[]" in bexI, auto)
        done
    next
      fix x
      assume "[[Event x]\<^sub>E] \<in> Q" "x \<notin> A"
      also have "[] \<in> P"
        by (simp add: TT_empty TT_P)
      then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[Event x]\<^sub>E] \<in> xa"
        using calculation apply (rule_tac x="[] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Event x]\<^sub>E]" in exI, auto)
        apply (rule_tac x="[]" in bexI, auto)
        apply (rule_tac x="[[Event x]\<^sub>E]" in bexI, auto)
        done
    qed
    have set2: "{Event ea |ea. ea \<in> A \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[Event ea]\<^sub>E] \<in> x)}
      \<subseteq> {Event ea |ea. ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> P} \<inter> {Event ea |ea. ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> P}"
    proof (auto, case_tac "(p,q)" rule:ttWF2.cases, auto)
      fix \<rho> f \<sigma>
      assume "[Event f]\<^sub>E # \<rho> \<in> P"
      also have "TT1 P"
        using TT_P TT_def by blast
      then show "[[Event f]\<^sub>E] \<in> P"
        using calculation unfolding TT1_def apply auto
        by (erule_tac x="[[Event f]\<^sub>E]" in allE, auto)
    qed
    have set3: "{e. e = Tick \<and> [[Tick]\<^sub>E] \<in> P} \<inter> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> Q} \<subseteq> {e. e = Tick \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[Tick]\<^sub>E] \<in> x)}"
    proof auto
      fix x
      assume "[[Tick]\<^sub>E] \<in> P" "[[Tick]\<^sub>E] \<in> Q"
      then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[Tick]\<^sub>E] \<in> xa"
        apply (rule_tac x="[[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" in exI, auto)
        apply (rule_tac x="[[Tick]\<^sub>E]" in bexI, auto)+
        done
    qed
    have set4: "{e. e = Tock \<and> [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P} \<inter> {e. e = Tock \<and> [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q} \<subseteq> {e. e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X]\<^sub>R, [Tock]\<^sub>E] \<in> x)}"
    proof auto
      fix x
      assume "[[X]\<^sub>R, [Tock]\<^sub>E] \<in> P" "[[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
      then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X]\<^sub>R, [Tock]\<^sub>E] \<in> x"
        apply (rule_tac x="[[X]\<^sub>R, [Tock]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[X]\<^sub>R, [Tock]\<^sub>E]" in exI, auto)
        apply (rule_tac x="[[X]\<^sub>R, [Tock]\<^sub>E]" in bexI, auto)+
        done
    qed
    have Tock_cases: "Tock \<in> Y \<Longrightarrow> 
      ([[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<and> [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> Q)
        \<or> ([[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<and> [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q)
        \<or> ([[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<and> [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> Q)"
    proof -
      assume Tock_in_Y: "Tock \<in> Y"
      have "{e\<in>Y. e = Tock} \<inter> {e. e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X]\<^sub>R, [Tock]\<^sub>E] \<in> x)} = {}"
        using assm1 by auto
      then have "{e\<in>Y. e = Tock} \<inter> {e. e = Tock \<and> [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P} \<inter> {e. e = Tock \<and> [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q} = {}"
        using set4 by fastforce
      then have "Tock \<notin> {e. e = Tock \<and> [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P} \<inter> {e. e = Tock \<and> [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q}"
        using Tock_in_Y by blast
      then show "([[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<and> [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> Q)
        \<or> ([[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<and> [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q) \<or> ([[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<and> [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> Q)"
        by auto
    qed
    have Tick_cases: "Tick \<in> Y \<Longrightarrow> [[Tick]\<^sub>E] \<notin> P \<or> [[Tick]\<^sub>E] \<notin> Q"
    proof -
      assume Tick_in_Y: "Tick \<in> Y"
      have "{e\<in>Y. e = Tick} \<inter> {e. e = Tick \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[Tick]\<^sub>E] \<in> x)} = {}"
        using assm1 by blast
      then have "{e\<in>Y. e = Tick} \<inter> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> P} \<inter> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> Q} = {}"
        by fastforce
      then have "Tick \<notin> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> P} \<inter> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> Q}"
        using Tick_in_Y by blast
      then show "[[Tick]\<^sub>E] \<notin> P \<or> [[Tick]\<^sub>E] \<notin> Q"
        by auto
    qed
    have X_Tock_notin_parcomp: "Tock \<in> Y \<Longrightarrow> [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<lbrakk>A\<rbrakk>\<^sub>C Q"
    proof -
      assume Tock_in_Y: "Tock \<in> Y"
      then have Y_Tock: "{e\<in>Y. e = Tock} \<inter> {e. e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X]\<^sub>R, [Tock]\<^sub>E] \<in> x)} = {}"
        using assm1 by auto
      have "Tock \<notin> {e. e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X]\<^sub>R, [Tock]\<^sub>E] \<in> x)}"
        using Y_Tock Tock_in_Y by blast
      then show "[[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<lbrakk>A\<rbrakk>\<^sub>C Q"
        unfolding ParCompTT_def by simp
    qed
    have nontock_sets: "\<exists> B C. Y \<inter> (Event ` A \<union> {Tick}) = B \<union> C
        \<and> B \<inter> ({e. \<exists> ea. e = Event ea \<and> ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> P} \<union> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> P}) = {}
        \<and> C \<inter> ({e. \<exists> ea. e = Event ea \<and> ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> Q} \<union> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> Q}) = {}"
    proof -
      have 1: "(Y \<inter> (Event ` A \<union> {Tick})) \<inter> ({e. \<exists> ea. e = Event ea \<and> ea \<in> A \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[Event ea]\<^sub>E] \<in> x)} \<union> {e. e = Tick \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[Tick]\<^sub>E] \<in> x)}) = {}"
        using assm1 by blast
      have 2: "(Y \<inter> (Event ` A \<union> {Tick})) \<inter> ({e. \<exists> ea. e = Event ea \<and> ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> P} \<union> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> P}) \<inter> ({e. \<exists> ea. e = Event ea \<and> ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> Q} \<union> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> Q})
        \<subseteq> (Y \<inter> (Event ` A \<union> {Tick})) \<inter> ({e. \<exists> ea. e = Event ea \<and> ea \<in> A \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[Event ea]\<^sub>E] \<in> x)} \<union> {e. e = Tick \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[Tick]\<^sub>E] \<in> x)})"
        apply auto
        using Tick_cases apply blast
        using set2 apply force
        apply (subgoal_tac "False", auto)
        using set2 apply force
        done
      have "(Y \<inter> (Event ` A \<union> {Tick})) \<inter> ({e. \<exists> ea. e = Event ea \<and> ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> P} \<union> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> P}) \<inter> ({e. \<exists> ea. e = Event ea \<and> ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> Q} \<union> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> Q}) \<subseteq> {}"
        using "1" apply simp
        using "2" by auto
      then have "(Y \<inter> (Event ` A \<union> {Tick})) \<inter> ({e. \<exists> ea. e = Event ea \<and> ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> P} \<union> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> P}) \<inter> ({e. \<exists> ea. e = Event ea \<and> ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> Q} \<union> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> Q}) = {}"
        by auto
      then have "\<forall>x\<in>Y \<inter> (Event ` A \<union> {Tick}). x \<notin> ({e. \<exists> ea. e = Event ea \<and> ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> P} \<union> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> P}) \<inter> ({e. \<exists> ea. e = Event ea \<and> ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> Q} \<union> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> Q})"
        by auto
      then have "\<forall>x\<in>Y \<inter> (Event ` A \<union> {Tick}). x \<notin> ({e. \<exists> ea. e = Event ea \<and> ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> P} \<union> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> P}) \<or> x \<notin> ({e. \<exists> ea. e = Event ea \<and> ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> Q} \<union> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> Q})"
        by auto
      then show ?thesis
        apply (rule_tac x="{x\<in>Y \<inter> (Event ` A \<union> {Tick}). x \<notin> ({e. \<exists> ea. e = Event ea \<and> ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> P} \<union> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> P})}" in exI)
        apply (rule_tac x="{x\<in>Y \<inter> (Event ` A \<union> {Tick}). x \<notin> ({e. \<exists> ea. e = Event ea \<and> ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> Q} \<union> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> Q})}" in exI)
        by auto
    qed
    show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X \<union> Y]\<^sub>R] \<in> x"
      using p_q_cases
    proof safe
      fix Z W
      assume p_Z: "p = [[Z]\<^sub>R]"
      assume q_W: "q = [[W]\<^sub>R]"
      assume X_subset_Z_W: "X \<subseteq> Z \<union> W"
      assume Z_W_part_eq: "{e \<in> Z. e \<notin> Event ` A \<union> {Tock, Tick}} = {e \<in> W. e \<notin> Event ` A \<union> {Tock, Tick}}"
      show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X \<union> Y]\<^sub>R] \<in> x"
      proof (cases "Tock \<in> Y")
        assume Tock_in_Y: "Tock \<in> Y"
        then have "{e\<in>Y. e = Tock} \<inter> {e. e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X]\<^sub>R, [Tock]\<^sub>E] \<in> x)} = {}"
          using assm1 by auto
        then have "Tock \<notin> {e. e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X]\<^sub>R, [Tock]\<^sub>E] \<in> x)}"
          using Tock_in_Y by blast
        then have X_Tock_notin_parcomp: "[[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<lbrakk>A\<rbrakk>\<^sub>C Q"
          unfolding ParCompTT_def by simp
        then have "[[X \<inter> W]\<^sub>R, [Tock]\<^sub>E] \<notin> Q \<or> [[X \<inter> Z]\<^sub>R, [Tock]\<^sub>E] \<notin> P"
        proof (safe, simp_all)                                       
          have "[[X]\<^sub>R, [Tock]\<^sub>E] \<in> [[X \<inter> W]\<^sub>R, [Tock]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[X \<inter> Z]\<^sub>R, [Tock]\<^sub>E]"
            using X_subset_Z_W Z_W_part_eq by auto
          also assume "[[X \<inter> Z]\<^sub>R, [Tock]\<^sub>E] \<in> P" "[[X \<inter> W]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
          then have "[[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<lbrakk>A\<rbrakk>\<^sub>C Q"
            unfolding ParCompTT_def using calculation apply simp
            apply (rule_tac x="[[X \<inter> W]\<^sub>R, [Tock]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[X \<inter> Z]\<^sub>R, [Tock]\<^sub>E]" in exI, simp)
            apply (rule_tac x="[[X \<inter> Z]\<^sub>R, [Tock]\<^sub>E]" in bexI, simp_all)
            apply (rule_tac x="[[X \<inter> W]\<^sub>R, [Tock]\<^sub>E]" in bexI, simp_all, blast)
            done
          then show "False"
            using X_Tock_notin_parcomp by auto
        qed
        then have W_Z_Tock_cases: "[[W]\<^sub>R, [Tock]\<^sub>E] \<notin> Q \<or> [[Z]\<^sub>R, [Tock]\<^sub>E] \<notin> P"
        proof auto
          have TT1_Q: "TT1 Q"
            by (simp add: TT_TT1 TT_Q)
          assume "[[W]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
          then have "[[X \<inter> W]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
            using TT1_Q unfolding TT1_def by force
          also assume "[[X \<inter> W]\<^sub>R, [Tock]\<^sub>E] \<notin> Q"
          then show "False"
            using calculation by auto
        next
          have TT1_P: "TT1 P"
            by (simp add: TT_TT1 TT_P)
          assume "[[Z]\<^sub>R, [Tock]\<^sub>E] \<in> P"
          then have "[[X \<inter> Z]\<^sub>R, [Tock]\<^sub>E] \<in> P"
            using TT1_P unfolding TT1_def by force
          also assume "[[X \<inter> Z]\<^sub>R, [Tock]\<^sub>E] \<notin> P"
          then show "False"
            using calculation by auto
        qed
        show ?thesis
          using W_Z_Tock_cases nontock_sets
        proof auto
          fix B C
          assume Y_B_C: "Y \<inter> insert Tick (Event ` A) = B \<union> C"
          assume B_intersect: "B \<inter> ({Event ea |ea. ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> P} \<union> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> P}) = {}"
          assume C_intersect: "C \<inter> ({Event ea |ea. ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> Q} \<union> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> Q}) = {}"
          assume Tock_notin_Q: "[[W]\<^sub>R, [Tock]\<^sub>E] \<notin> Q"
          
          have 1: "(C \<union> {Event ea |ea. ea \<notin> A \<and> Event ea \<in> Y} \<union> {Tock}) \<inter> {e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> [[W]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
          proof -
            have "{e. \<exists> ea. e = Event ea \<and> ea \<notin> A} \<inter> Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[e]\<^sub>E] \<in> x) \<or>
              e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> x)} = {e. \<exists> ea. e = Event ea \<and> ea \<notin> A} \<inter> {}"
              using assm1 by (simp add: inf_assoc)
            then have "{e. \<exists> ea. e = Event ea \<and> ea \<notin> A} \<inter> Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[e]\<^sub>E] \<in> x) \<or>
              e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> x)} = {}"
              using assm1 by simp
            then have "{e. \<exists> ea. e = Event ea \<and> ea \<notin> A \<and> Event ea \<in> Y} \<inter> {Event ea |ea. ea \<notin> A \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[Event ea]\<^sub>E] \<in> x)} = {}"
              by blast
            then have "{e. \<exists> ea. e = Event ea \<and> ea \<notin> A \<and> Event ea \<in> Y} \<inter> ({Event ea |ea. ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> P} \<union> {Event ea |ea. ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> Q}) = {}"
              using set1 by (smt inf.orderE inf_assoc inf_bot_left inf_sup_aci(1)) 
            then have "{e. \<exists> ea. e = Event ea \<and> ea \<notin> A \<and> Event ea \<in> Y} \<inter> {Event ea |ea. ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> Q} = {}"
              by auto
            then show ?thesis
              using C_intersect Tock_notin_Q Y_B_C by (auto, case_tac x, auto, case_tac "x1 \<in> A", auto)
          qed

          have 2: "(B \<union> {Event ea |ea. ea \<notin> A \<and> Event ea \<in> Y}) \<inter> {e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> [[Z]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
          proof -
            have "{e. \<exists> ea. e = Event ea \<and> ea \<notin> A} \<inter> Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[e]\<^sub>E] \<in> x) \<or>
              e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> x)} = {e. \<exists> ea. e = Event ea \<and> ea \<notin> A} \<inter> {}"
              using assm1 by (simp add: inf_assoc)
            then have "{e. \<exists> ea. e = Event ea \<and> ea \<notin> A} \<inter> Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[e]\<^sub>E] \<in> x) \<or>
              e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> x)} = {}"
              using assm1 by simp
            then have "{e. \<exists> ea. e = Event ea \<and> ea \<notin> A \<and> Event ea \<in> Y} \<inter> {Event ea |ea. ea \<notin> A \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[Event ea]\<^sub>E] \<in> x)} = {}"
              by blast
            then have "{e. \<exists> ea. e = Event ea \<and> ea \<notin> A \<and> Event ea \<in> Y} \<inter> ({Event ea |ea. ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> P} \<union> {Event ea |ea. ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> Q}) = {}"
              using set1 by (smt inf.orderE inf_assoc inf_bot_left inf_sup_aci(1)) 
            then have "{e. \<exists> ea. e = Event ea \<and> ea \<notin> A \<and> Event ea \<in> Y} \<inter> {Event ea |ea. ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> P} = {}"
              by auto
            then show ?thesis
              using B_intersect Y_B_C by (auto, case_tac x, auto, case_tac "x1 \<in> A", auto)
          qed

          have 3: "[[Z \<union> (B \<union> {Event ea |ea. ea \<notin> A \<and> Event ea \<in> Y})]\<^sub>R] \<in> P"
          proof -
            have "TT2w P"
              using TT_P TT_def by blast
            also have "[[Z]\<^sub>R] \<in> P"
              using p_P p_Z by blast
            then show "[[Z \<union> (B \<union> {Event ea |ea. ea \<notin> A \<and> Event ea \<in> Y})]\<^sub>R] \<in> P"
              using calculation 2 unfolding TT2w_def
              apply (erule_tac x="[]" in allE)
              apply (erule_tac x="Z" in allE)
              apply (erule_tac x="(B \<union> {Event ea |ea. ea \<notin> A \<and> Event ea \<in> Y})" in allE, auto)
              done
          qed

          have 4: "[[W \<union> (C \<union> {Event ea |ea. ea \<notin> A \<and> Event ea \<in> Y} \<union> {Tock})]\<^sub>R] \<in> Q"
          proof -
            have "TT2w Q"
              using TT_Q TT_def by blast
            also have "[[W]\<^sub>R] \<in> Q"
              using q_Q q_W by blast
            then show "[[W \<union> (C \<union> {Event ea |ea. ea \<notin> A \<and> Event ea \<in> Y} \<union> {Tock})]\<^sub>R] \<in> Q"
              using calculation 1 unfolding TT2w_def
              apply (erule_tac x="[]" in allE)
              apply (erule_tac x="W" in allE)
              apply (erule_tac x="(C \<union> {Event ea |ea. ea \<notin> A \<and> Event ea \<in> Y} \<union> {Tock})" in allE, auto)
              done
          qed

          show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X \<union> Y]\<^sub>R] \<in> x"
            using 3 4  apply auto
            apply (rule_tac x="[[Z \<union> (B \<union> {Event ea |ea. ea \<notin> A \<and> Event ea \<in> Y})]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[W \<union> (C \<union> {Event ea |ea. ea \<notin> A \<and> Event ea \<in> Y} \<union> {Tock})]\<^sub>R]" in exI, safe, simp_all)
            apply (rule_tac x="[[Z \<union> (B \<union> {Event ea |ea. ea \<notin> A \<and> Event ea \<in> Y})]\<^sub>R]" in bexI, simp_all)
            apply (rule_tac x="[[W \<union> (C \<union> {Event ea |ea. ea \<notin> A \<and> Event ea \<in> Y} \<union> {Tock})]\<^sub>R]" in bexI, auto)
            using Z_W_part_eq X_subset_Z_W apply (blast)
            apply (case_tac x, auto, case_tac "x1 \<in> A", auto)
            apply (insert Z_W_part_eq X_subset_Z_W Y_B_C, blast)+
            done
        next
          fix B C
          assume Y_B_C: "Y \<inter> insert Tick (Event ` A) = B \<union> C"
          assume B_intersect: "B \<inter> ({Event ea |ea. ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> P} \<union> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> P}) = {}"
          assume C_intersect: "C \<inter> ({Event ea |ea. ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> Q} \<union> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> Q}) = {}"
          assume Tock_notin_P: "[[Z]\<^sub>R, [Tock]\<^sub>E] \<notin> P"
          
          have 1: "(C \<union> {Event ea |ea. ea \<notin> A \<and> Event ea \<in> Y}) \<inter> {e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> [[W]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
          proof -
            have "{e. \<exists> ea. e = Event ea \<and> ea \<notin> A} \<inter> Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[e]\<^sub>E] \<in> x) \<or>
              e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> x)} = {e. \<exists> ea. e = Event ea \<and> ea \<notin> A} \<inter> {}"
              using assm1 by (simp add: inf_assoc)
            then have "{e. \<exists> ea. e = Event ea \<and> ea \<notin> A} \<inter> Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[e]\<^sub>E] \<in> x) \<or>
              e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> x)} = {}"
              using assm1 by simp
            then have "{e. \<exists> ea. e = Event ea \<and> ea \<notin> A \<and> Event ea \<in> Y} \<inter> {Event ea |ea. ea \<notin> A \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[Event ea]\<^sub>E] \<in> x)} = {}"
              by blast
            then have "{e. \<exists> ea. e = Event ea \<and> ea \<notin> A \<and> Event ea \<in> Y} \<inter> ({Event ea |ea. ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> P} \<union> {Event ea |ea. ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> Q}) = {}"
              using set1 by (smt inf.orderE inf_assoc inf_bot_left inf_sup_aci(1)) 
            then have "{e. \<exists> ea. e = Event ea \<and> ea \<notin> A \<and> Event ea \<in> Y} \<inter> {Event ea |ea. ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> Q} = {}"
              by auto
            then show ?thesis
              using C_intersect Y_B_C by (auto, case_tac x, auto, case_tac "x1 \<in> A", auto)
          qed

          have 2: "(B \<union> {Event ea |ea. ea \<notin> A \<and> Event ea \<in> Y} \<union> {Tock}) \<inter> {e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> [[Z]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
          proof -
            have "{e. \<exists> ea. e = Event ea \<and> ea \<notin> A} \<inter> Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[e]\<^sub>E] \<in> x) \<or>
              e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> x)} = {e. \<exists> ea. e = Event ea \<and> ea \<notin> A} \<inter> {}"
              using assm1 by (simp add: inf_assoc)
            then have "{e. \<exists> ea. e = Event ea \<and> ea \<notin> A} \<inter> Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[e]\<^sub>E] \<in> x) \<or>
              e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> x)} = {}"
              using assm1 by simp
            then have "{e. \<exists> ea. e = Event ea \<and> ea \<notin> A \<and> Event ea \<in> Y} \<inter> {Event ea |ea. ea \<notin> A \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[Event ea]\<^sub>E] \<in> x)} = {}"
              by blast
            then have "{e. \<exists> ea. e = Event ea \<and> ea \<notin> A \<and> Event ea \<in> Y} \<inter> ({Event ea |ea. ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> P} \<union> {Event ea |ea. ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> Q}) = {}"
              using set1 by (smt inf.orderE inf_assoc inf_bot_left inf_sup_aci(1)) 
            then have "{e. \<exists> ea. e = Event ea \<and> ea \<notin> A \<and> Event ea \<in> Y} \<inter> {Event ea |ea. ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> P} = {}"
              by auto
            then show ?thesis
              using B_intersect Tock_notin_P Y_B_C by (auto, case_tac x, auto, case_tac "x1 \<in> A", auto)
          qed

          have 3: "[[Z \<union> (B \<union> {Event ea |ea. ea \<notin> A \<and> Event ea \<in> Y} \<union> {Tock})]\<^sub>R] \<in> P"
          proof -
            have "TT2w P"
              using TT_P TT_def by blast
            also have "[[Z]\<^sub>R] \<in> P"
              using p_P p_Z by blast
            then show "[[Z \<union> (B \<union> {Event ea |ea. ea \<notin> A \<and> Event ea \<in> Y} \<union> {Tock})]\<^sub>R] \<in> P"
              using calculation 2 unfolding TT2w_def
              apply (erule_tac x="[]" in allE)
              apply (erule_tac x="Z" in allE)
              apply (erule_tac x="(B \<union> {Event ea |ea. ea \<notin> A \<and> Event ea \<in> Y} \<union> {Tock})" in allE, auto)
              done
          qed

          have 4: "[[W \<union> (C \<union> {Event ea |ea. ea \<notin> A \<and> Event ea \<in> Y})]\<^sub>R] \<in> Q"
          proof -
            have "TT2w Q"
              using TT_Q TT_def by blast
            also have "[[W]\<^sub>R] \<in> Q"
              using q_Q q_W by blast
            then show "[[W \<union> (C \<union> {Event ea |ea. ea \<notin> A \<and> Event ea \<in> Y})]\<^sub>R] \<in> Q"
              using calculation 1 unfolding TT2w_def
              apply (erule_tac x="[]" in allE)
              apply (erule_tac x="W" in allE)
              apply (erule_tac x="(C \<union> {Event ea |ea. ea \<notin> A \<and> Event ea \<in> Y})" in allE, auto)
              done
          qed

          show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X \<union> Y]\<^sub>R] \<in> x"
            using 3 4  apply auto
            apply (rule_tac x="[[Z \<union> (B \<union> {Event ea |ea. ea \<notin> A \<and> Event ea \<in> Y})]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[W \<union> (C \<union> {Event ea |ea. ea \<notin> A \<and> Event ea \<in> Y} \<union> {Tock})]\<^sub>R]" in exI, safe, simp_all)
            apply (rule_tac x="[[Z \<union> (B \<union> {Event ea |ea. ea \<notin> A \<and> Event ea \<in> Y} \<union> {Tock})]\<^sub>R]" in bexI, simp_all)
            apply (rule_tac x="[[W \<union> (C \<union> {Event ea |ea. ea \<notin> A \<and> Event ea \<in> Y})]\<^sub>R]" in bexI, auto)
            using Z_W_part_eq X_subset_Z_W apply (blast)
            apply (case_tac x, auto, case_tac "x1 \<in> A", auto)
            apply (insert Z_W_part_eq X_subset_Z_W Y_B_C, blast)+
            done
        qed
      next
        assume Tock_notin_Y: "Tock \<notin> Y"

        obtain B C where Y_B_C: "Y \<inter> insert Tick (Event ` A) = B \<union> C"
          and B_intersect: "B \<inter> ({Event ea |ea. ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> P} \<union> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> P}) = {}"
          and C_intersect: "C \<inter> ({Event ea |ea. ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> Q} \<union> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> Q}) = {}"
          using nontock_sets by auto
          
          
        have 1: "(C \<union> {Event ea |ea. ea \<notin> A \<and> Event ea \<in> Y}) \<inter> {e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> [[W]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
        proof -
          have "{e. \<exists> ea. e = Event ea \<and> ea \<notin> A} \<inter> Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[e]\<^sub>E] \<in> x) \<or>
            e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> x)} = {e. \<exists> ea. e = Event ea \<and> ea \<notin> A} \<inter> {}"
            using assm1 by (simp add: inf_assoc)
          then have "{e. \<exists> ea. e = Event ea \<and> ea \<notin> A} \<inter> Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[e]\<^sub>E] \<in> x) \<or>
            e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> x)} = {}"
            using assm1 by simp
          then have "{e. \<exists> ea. e = Event ea \<and> ea \<notin> A \<and> Event ea \<in> Y} \<inter> {Event ea |ea. ea \<notin> A \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[Event ea]\<^sub>E] \<in> x)} = {}"
            by blast
          then have "{e. \<exists> ea. e = Event ea \<and> ea \<notin> A \<and> Event ea \<in> Y} \<inter> ({Event ea |ea. ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> P} \<union> {Event ea |ea. ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> Q}) = {}"
            using set1 by (smt inf.orderE inf_assoc inf_bot_left inf_sup_aci(1)) 
          then have "{e. \<exists> ea. e = Event ea \<and> ea \<notin> A \<and> Event ea \<in> Y} \<inter> {Event ea |ea. ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> Q} = {}"
            by auto
          then show ?thesis
            using C_intersect Y_B_C by (auto, case_tac x, auto, case_tac "x1 \<in> A", auto)
        qed

        have 2: "(B \<union> {Event ea |ea. ea \<notin> A \<and> Event ea \<in> Y}) \<inter> {e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> [[Z]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
        proof -
          have "{e. \<exists> ea. e = Event ea \<and> ea \<notin> A} \<inter> Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[e]\<^sub>E] \<in> x) \<or>
            e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> x)} = {e. \<exists> ea. e = Event ea \<and> ea \<notin> A} \<inter> {}"
            using assm1 by (simp add: inf_assoc)
          then have "{e. \<exists> ea. e = Event ea \<and> ea \<notin> A} \<inter> Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[e]\<^sub>E] \<in> x) \<or>
            e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> x)} = {}"
            using assm1 by simp
          then have "{e. \<exists> ea. e = Event ea \<and> ea \<notin> A \<and> Event ea \<in> Y} \<inter> {Event ea |ea. ea \<notin> A \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[Event ea]\<^sub>E] \<in> x)} = {}"
            by blast
          then have "{e. \<exists> ea. e = Event ea \<and> ea \<notin> A \<and> Event ea \<in> Y} \<inter> ({Event ea |ea. ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> P} \<union> {Event ea |ea. ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> Q}) = {}"
            using set1 by (smt inf.orderE inf_assoc inf_bot_left inf_sup_aci(1)) 
          then have "{e. \<exists> ea. e = Event ea \<and> ea \<notin> A \<and> Event ea \<in> Y} \<inter> {Event ea |ea. ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> P} = {}"
            by auto
          then show ?thesis
            using B_intersect Y_B_C by (auto, case_tac x, auto, case_tac "x1 \<in> A", auto)
        qed

        have 3: "[[Z \<union> (B \<union> {Event ea |ea. ea \<notin> A \<and> Event ea \<in> Y})]\<^sub>R] \<in> P"
        proof -
          have "TT2w P"
            using TT_P TT_def by blast
          also have "[[Z]\<^sub>R] \<in> P"
            using p_P p_Z by blast
          then show "[[Z \<union> (B \<union> {Event ea |ea. ea \<notin> A \<and> Event ea \<in> Y})]\<^sub>R] \<in> P"
            using calculation 2 unfolding TT2w_def
            apply (erule_tac x="[]" in allE)
            apply (erule_tac x="Z" in allE)
            apply (erule_tac x="(B \<union> {Event ea |ea. ea \<notin> A \<and> Event ea \<in> Y})" in allE, auto)
            done
        qed

        have 4: "[[W \<union> (C \<union> {Event ea |ea. ea \<notin> A \<and> Event ea \<in> Y})]\<^sub>R] \<in> Q"
        proof -
          have "TT2w Q"
            using TT_Q TT_def by blast
          also have "[[W]\<^sub>R] \<in> Q"
            using q_Q q_W by blast
          then show "[[W \<union> (C \<union> {Event ea |ea. ea \<notin> A \<and> Event ea \<in> Y})]\<^sub>R] \<in> Q"
            using calculation 1 unfolding TT2w_def
            apply (erule_tac x="[]" in allE)
            apply (erule_tac x="W" in allE)
            apply (erule_tac x="(C \<union> {Event ea |ea. ea \<notin> A \<and> Event ea \<in> Y})" in allE, auto)
            done
        qed

        show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X \<union> Y]\<^sub>R] \<in> x"
          using 3 4 apply -
          apply (rule_tac x="[[Z \<union> (B \<union> {Event ea |ea. ea \<notin> A \<and> Event ea \<in> Y})]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[W \<union> (C \<union> {Event ea |ea. ea \<notin> A \<and> Event ea \<in> Y})]\<^sub>R]" in exI, safe, simp_all)
          apply (rule_tac x="[[Z \<union> (B \<union> {Event ea |ea. ea \<notin> A \<and> Event ea \<in> Y})]\<^sub>R]" in bexI, simp_all)
          apply (rule_tac x="[[W \<union> (C \<union> {Event ea |ea. ea \<notin> A \<and> Event ea \<in> Y})]\<^sub>R]" in bexI, safe, simp_all)
          using Z_W_part_eq Tock_notin_Y X_subset_Z_W apply (blast)
          apply (case_tac x, auto, case_tac "x1 \<in> A", auto, case_tac "x1 \<in> A", auto)
          apply (insert Z_W_part_eq Tock_notin_Y X_subset_Z_W Y_B_C, blast)+
          done
      qed
    next
      fix Z B
      assume p_Z: "p = [[Z]\<^sub>R]"
      assume q_Tick: "q = [[Tick]\<^sub>E]"
      assume X_subset_Z_Tick: "X = Z \<union> Event ` B"
      assume B_subset_A: "B \<subseteq> A"
      have case1: "{x\<in>Y. x \<notin> Event ` A \<and> x \<noteq> Tick \<and> x \<noteq> Tock} \<inter> {Event ea |ea. ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> P} = {}"
      proof -
        have "{x\<in>Y. x \<notin> Event ` A \<and> x \<noteq> Tick \<and> x \<noteq> Tock} \<inter> {Event ea |ea. ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> P}
          \<subseteq> {x\<in>Y. x \<notin> Event ` A \<and> x \<noteq> Tick \<and> x \<noteq> Tock}
            \<inter> {Event ea |ea. ea \<notin> A \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[Event ea]\<^sub>E] \<in> x)}"
          using set1 by blast
        then have "{x\<in>Y. x \<notin> Event ` A \<and> x \<noteq> Tick \<and> x \<noteq> Tock} \<inter> {Event ea |ea. ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> P}
          \<subseteq> Y \<inter>
            {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[e]\<^sub>E] \<in> x) \<or>
              e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> x)}"
          by force
        then show "{x\<in>Y. x \<notin> Event ` A \<and> x \<noteq> Tick \<and> x \<noteq> Tock} \<inter> {Event ea |ea. ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> P} ={}"
          using assm1 by auto
      qed
      have case2: "{x\<in>Y. x = Tick} \<inter> {x. x = Tick \<and> [[Tick]\<^sub>E] \<in> P} = {}"
      proof (cases "Tick \<in> Y", auto)
        assume Tick_in_Y: "Tick \<in> Y"
        assume Tick_in_P: "[[Tick]\<^sub>E] \<in> P"
        have "[[Tick]\<^sub>E] \<in> P \<lbrakk>A\<rbrakk>\<^sub>C Q"
          unfolding ParCompTT_def using Tick_in_P q_Tick q_Q apply auto
          apply (rule_tac x="[[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" in exI, auto)
          by (rule_tac x="[[Tick]\<^sub>E]" in bexI, rule_tac x="[[Tick]\<^sub>E]" in bexI, auto)
        then show False
          using Tick_in_Y Tick_cases Tick_in_P q_Q q_Tick by blast
      qed
      have case3: "{x\<in>Y. x = Tock} \<inter> {x. x = Tock \<and> [[Z]\<^sub>R, [Tock]\<^sub>E] \<in> P} = {}"
      proof (cases "Tock \<in> Y", auto)
        assume Tock_in_Y: "Tock \<in> Y"
        assume Tock_in_P: "[[Z]\<^sub>R, [Tock]\<^sub>E] \<in> P"
        have "{e\<in>Y. e = Tock} \<inter> {e. e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X]\<^sub>R, [Tock]\<^sub>E] \<in> x)} = {}"
            using assm1 by auto
          then have "Tock \<notin> {e. e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X]\<^sub>R, [Tock]\<^sub>E] \<in> x)}"
            using Tock_in_Y by blast
          then have X_Tock_notin_parcomp: "[[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<lbrakk>A\<rbrakk>\<^sub>C Q"
            unfolding ParCompTT_def by simp  
          also have "[[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<lbrakk>A\<rbrakk>\<^sub>C Q"
            unfolding ParCompTT_def using Tock_in_P q_Q q_Tick X_subset_Z_Tick B_subset_A apply simp
            apply (rule_tac x="[[Z]\<^sub>R, [Tock]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" in exI, safe, simp_all)
            apply (rule_tac x="[[Z]\<^sub>R, [Tock]\<^sub>E]" in bexI, simp_all)
            apply (rule_tac x="[[Tick]\<^sub>E]" in bexI, auto)
            done
          then show "False"
            using calculation by auto
        qed
      have "{e\<in>Y. e \<notin> Event ` A} \<inter> {e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> [[Z]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
      proof -
        have 1: "{e\<in>Y. e \<notin> Event ` A} =
          {x \<in> Y. x \<notin> Event ` A \<and> x \<noteq> Tick \<and> x \<noteq> Tock} \<union> {x \<in> Y. x = Tick} \<union> {x \<in> Y. x = Tock} \<union> {}"
          by auto
        have 2: "{e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> [[Z]\<^sub>R, [e]\<^sub>E] \<in> P} = 
          {Event ea |ea. ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> P} \<union> {x. x = Tick \<and> [[Tick]\<^sub>E] \<in> P}
            \<union> {x. x = Tock \<and> [[Z]\<^sub>R, [Tock]\<^sub>E] \<in> P} \<union> {Event ea |ea. ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> P}"
          by (auto, (metis ttevent.exhaust)+)
        show ?thesis
          using case1 case2 case3 1 2 by force
      qed
      then have "[[Z \<union> {e\<in>Y. e \<notin> Event ` A}]\<^sub>R] \<in> P"
        using TT2w_P p_Z p_P unfolding TT2w_def apply (erule_tac x="[]" in allE)
        by (erule_tac x="Z" in allE, erule_tac x="{e\<in>Y. e \<notin> Event ` A}" in allE, auto)
      then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[Z \<union> Event ` B \<union> Y]\<^sub>R] \<in> x"
        apply (rule_tac x= "[[Z \<union> {e\<in>Y. e \<notin> Event ` A}]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" in exI, simp, safe)
        apply (rule_tac x= "[[Z \<union> {e\<in>Y. e \<notin> Event ` A}]\<^sub>R]" in bexI, rule_tac x= "[[Tick]\<^sub>E]" in bexI)
        by (simp_all, metis q_Q q_Tick, rule_tac x=" B \<union> {e\<in>A. Event e \<in> Y}" in exI, auto simp add: B_subset_A)
    next
      fix W B
      assume q_W: "q = [[W]\<^sub>R]"
      assume p_Tick: "p = [[Tick]\<^sub>E]"
      assume X_subset_W_Tick: "X \<subseteq> Event ` B \<union> W"
      assume B_subset_A: "B \<subseteq> A"
      have case1: "{x\<in>Y. x \<notin> Event ` A \<and> x \<noteq> Tick \<and> x \<noteq> Tock} \<inter> {Event ea |ea. ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> Q} = {}"
      proof -
        have "{x\<in>Y. x \<notin> Event ` A \<and> x \<noteq> Tick \<and> x \<noteq> Tock} \<inter> {Event ea |ea. ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> Q}
          \<subseteq> {x\<in>Y. x \<notin> Event ` A \<and> x \<noteq> Tick \<and> x \<noteq> Tock}
            \<inter> {Event ea |ea. ea \<notin> A \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[Event ea]\<^sub>E] \<in> x)}"
          using set1 by blast
        then have "{x\<in>Y. x \<notin> Event ` A \<and> x \<noteq> Tick \<and> x \<noteq> Tock} \<inter> {Event ea |ea. ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> Q}
          \<subseteq> Y \<inter>
            {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[e]\<^sub>E] \<in> x) \<or>
              e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> x)}"
          by force
        then show "{x\<in>Y. x \<notin> Event ` A \<and> x \<noteq> Tick \<and> x \<noteq> Tock} \<inter> {Event ea |ea. ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> Q} ={}"
          using assm1 by auto
      qed
      have case2: "{x\<in>Y. x = Tick} \<inter> {x. x = Tick \<and> [[Tick]\<^sub>E] \<in> Q} = {}"
      proof (cases "Tick \<in> Y", auto)
        assume Tick_in_Y: "Tick \<in> Y"
        assume Tick_in_Q: "[[Tick]\<^sub>E] \<in> Q"
        have "[[Tick]\<^sub>E] \<in> P \<lbrakk>A\<rbrakk>\<^sub>C Q"
          unfolding ParCompTT_def using Tick_in_Q p_Tick p_P apply auto
          apply (rule_tac x="[[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" in exI, auto)
          by (rule_tac x="[[Tick]\<^sub>E]" in bexI, rule_tac x="[[Tick]\<^sub>E]" in bexI, auto)
        then show False
          using Tick_cases Tick_in_Q Tick_in_Y p_P p_Tick by blast
      qed
      have case3: "{x\<in>Y. x = Tock} \<inter> {x. x = Tock \<and> [[W]\<^sub>R, [Tock]\<^sub>E] \<in> Q} = {}"
      proof (cases "Tock \<in> Y", auto)
        assume Tock_in_Y: "Tock \<in> Y"
        assume Tock_in_P: "[[W]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
        have "{e\<in>Y. e = Tock} \<inter> {e. e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X]\<^sub>R, [Tock]\<^sub>E] \<in> x)} = {}"
          using assm1 by auto
        then have "Tock \<notin> {e. e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X]\<^sub>R, [Tock]\<^sub>E] \<in> x)}"
          using Tock_in_Y by blast
        then have X_Tock_notin_parcomp: "[[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<lbrakk>A\<rbrakk>\<^sub>C Q"
          unfolding ParCompTT_def by simp  
        also have "[[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<lbrakk>A\<rbrakk>\<^sub>C Q"
          unfolding ParCompTT_def using assm2 Tock_in_P p_P q_W p_Tick apply simp
          apply (rule_tac x="[[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[W]\<^sub>R, [Tock]\<^sub>E]" in exI, safe, simp_all)
          apply (rule_tac x="[[Tick]\<^sub>E]" in bexI, simp_all)
          apply (rule_tac x="[[W]\<^sub>R, [Tock]\<^sub>E]" in bexI, auto)
          done
        then show "False"
          using calculation by auto
      qed
      have "{e\<in>Y. e \<notin> Event ` A} \<inter> {e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> [[W]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
      proof -
        have 1: "{e\<in>Y. e \<notin> Event ` A} =
          {x \<in> Y. x \<notin> Event ` A \<and> x \<noteq> Tick \<and> x \<noteq> Tock} \<union> {x \<in> Y. x = Tick} \<union> {x \<in> Y. x = Tock} \<union> {}"
          by auto
        have 2: "{e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> [[W]\<^sub>R, [e]\<^sub>E] \<in> Q} = 
          {Event ea |ea. ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> Q} \<union> {x. x = Tick \<and> [[Tick]\<^sub>E] \<in> Q}
            \<union> {x. x = Tock \<and> [[W]\<^sub>R, [Tock]\<^sub>E] \<in> Q} \<union> {Event ea |ea. ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> Q}"
          by (auto, (metis ttevent.exhaust)+)
        show ?thesis
          using case1 case2 case3 1 2 by force
      qed
      then have "[[W \<union> {e\<in>Y. e \<notin> Event ` A}]\<^sub>R] \<in> Q"
        using TT2w_Q q_W q_Q unfolding TT2w_def apply (erule_tac x="[]" in allE)
        by (erule_tac x="W" in allE, erule_tac x="{e\<in>Y. e \<notin> Event ` A}" in allE, auto)
      then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X \<union> Y]\<^sub>R] \<in> x"
        using assm2 p_Tick q_W
        apply (rule_tac x="[[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[W \<union> {e\<in>Y. e \<notin> Event ` A}]\<^sub>R]" in exI, simp, safe)
        apply (rule_tac x="[[Tick]\<^sub>E]" in bexI, rule_tac x="[[W \<union> {e\<in>Y. e \<notin> Event ` A}]\<^sub>R]" in bexI)
        apply (simp_all, metis p_P p_Tick, rule_tac x="Aa \<union> {e\<in>A. Event e \<in> Y}" in exI, auto)
        done
    qed
  next
    fix X P Q Xa Y p q
    assume "[[X]\<^sub>R, [Xa]\<^sub>R] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "TT P" "TT Q" "p \<in> P" "q \<in> Q"
    then have "ttWF [[X]\<^sub>R, [Xa]\<^sub>R]"
      using TT_wf merge_traces_wf by blast
    then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X]\<^sub>R, [Xa \<union> Y]\<^sub>R] \<in> x"
      by simp
  next
    fix P Q X Y p q
    assume "[[Tick]\<^sub>E, [X]\<^sub>R] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "TT P" "TT Q" "p \<in> P" "q \<in> Q"
    then have "ttWF [[Tick]\<^sub>E, [X]\<^sub>R]"
      using TT_wf merge_traces_wf by blast
    then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[Tick]\<^sub>E, [X \<union> Y]\<^sub>R] \<in> x"
      by simp
  next
    fix P Q :: "'a ttobs list set"
    fix p q \<sigma> :: "'a ttobs list"
    fix X Y :: "'a ttevent set"  
    fix e :: "'a"
    assume assm1: "[Event e]\<^sub>E # \<sigma> @ [[X]\<^sub>R] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    then have p_q_cases: "(\<exists> p' q'. e \<in> A \<and> p = [Event e]\<^sub>E # p' \<and> q = [Event e]\<^sub>E # q')
      \<or> (\<exists> p'. e \<notin> A \<and> p = [Event e]\<^sub>E # p' \<and> \<sigma> @ [[X]\<^sub>R] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q)
      \<or> (\<exists> q'. e \<notin> A \<and> q = [Event e]\<^sub>E # q' \<and> \<sigma> @ [[X]\<^sub>R] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
      by (cases "(p,q)" rule:ttWF2.cases, simp_all, blast)
    assume induction_hypothesis: "(\<And>P Q X Y p q. TT P \<Longrightarrow> TT Q \<Longrightarrow>
      Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma> @ [[e]\<^sub>E] \<in> x) \<or>
        e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> x)} = {} \<Longrightarrow>
      \<sigma> @ [[X]\<^sub>R] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> p \<in> P \<Longrightarrow> q \<in> Q \<Longrightarrow> \<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma> @ [[X \<union> Y]\<^sub>R] \<in> x)"
    assume disjoint: "Y \<inter> {ea. ea \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Event e]\<^sub>E # \<sigma> @ [[ea]\<^sub>E] \<in> x) \<or>
                 ea = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Event e]\<^sub>E # \<sigma> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> x)} = {}"
    assume p_P: "p \<in> P" and q_Q: "q \<in> Q"
    assume TT_P: "TT P" and TT_Q: "TT Q"
    show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Event e]\<^sub>E # \<sigma> @ [[X \<union> Y]\<^sub>R] \<in> x"
      using p_q_cases
    proof auto
      fix p' q'
      assume e_in_A: "e \<in> A"
      assume p_def: "p = [Event e]\<^sub>E # p'"
      assume q_def: "q = [Event e]\<^sub>E # q'"
      have 1: "TT {t. [Event e]\<^sub>E # t \<in> P}"
        using TT_P TT_init_event p_P p_def by force
      have 2: "TT {t. [Event e]\<^sub>E # t \<in> Q}"
        using TT_Q TT_init_event q_Q q_def by force
      have 3: "Y \<inter> {ea. ea \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>{t. [Event e]\<^sub>E # t \<in> P}. \<exists>q\<in>{t. [Event e]\<^sub>E # t \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma> @ [[ea]\<^sub>E] \<in> x) \<or>
        ea = Tock \<and> (\<exists>x. (\<exists>p\<in>{t. [Event e]\<^sub>E # t \<in> P}. \<exists>q\<in>{t. [Event e]\<^sub>E # t \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> x)} = {}"
      proof -
        have "{ea. ea \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>{t. [Event e]\<^sub>E # t \<in> P}. \<exists>q\<in>{t. [Event e]\<^sub>E # t \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma> @ [[ea]\<^sub>E] \<in> x) \<or>
            ea = Tock \<and> (\<exists>x. (\<exists>p\<in>{t. [Event e]\<^sub>E # t \<in> P}. \<exists>q\<in>{t. [Event e]\<^sub>E # t \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> x)}
          \<subseteq> {ea. ea \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Event e]\<^sub>E # \<sigma> @ [[ea]\<^sub>E] \<in> x) \<or>
                 ea = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Event e]\<^sub>E # \<sigma> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> x)}"
          apply auto
          apply (rule_tac x="[Event e]\<^sub>E # p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event e]\<^sub>E # q" in exI, auto)
          apply (rule_tac x="[Event e]\<^sub>E # p" in bexI, auto)
          apply (rule_tac x="[Event e]\<^sub>E # q" in bexI, auto)
          using e_in_A apply linarith+
          apply (rule_tac x="[Event e]\<^sub>E # p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event e]\<^sub>E # q" in exI, auto)
          apply (rule_tac x="[Event e]\<^sub>E # p" in bexI, auto)
          apply (rule_tac x="[Event e]\<^sub>E # q" in bexI, auto)
          using e_in_A apply linarith+
          apply (erule_tac x="[Event e]\<^sub>E # p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event e]\<^sub>E # q" in allE, auto)
          apply (erule_tac x="[Event e]\<^sub>E # p" in ballE, auto)
          using e_in_A apply linarith+
          apply (erule_tac x="[Event e]\<^sub>E # p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event e]\<^sub>E # q" in allE, auto)
          apply (erule_tac x="[Event e]\<^sub>E # p" in ballE, auto)
          using e_in_A apply linarith+
          done
        then show ?thesis
          using disjoint by blast
      qed
      have 4: "\<sigma> @ [[X]\<^sub>R] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'"
        using e_in_A p_def q_def assm1 by auto
      have 5: "p' \<in> {t. [Event e]\<^sub>E # t \<in> P}"
        using p_P p_def by auto 
      have 6: "q' \<in> {t. [Event e]\<^sub>E # t \<in> Q}"
        using q_Q q_def by auto
      have "\<exists>p''\<in>{t. [Event e]\<^sub>E # t \<in> P}. \<exists>q''\<in>{t. [Event e]\<^sub>E # t \<in> Q}. \<sigma> @ [[X \<union> Y]\<^sub>R] \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q''"
        using induction_hypothesis[where P="{t. [Event e]\<^sub>E # t \<in> P}", where Q="{t. [Event e]\<^sub>E # t \<in> Q}", where p=p', where q=q', where X=X, where Y=Y]
        using 1 2 3 4 5 6 by auto
      then obtain p'' q'' where "p''\<in>{t. [Event e]\<^sub>E # t \<in> P}" "q''\<in>{t. [Event e]\<^sub>E # t \<in> Q}" "\<sigma> @ [[X \<union> Y]\<^sub>R] \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q''"
        by auto
      then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Event e]\<^sub>E # \<sigma> @ [[X \<union> Y]\<^sub>R] \<in> x"
        apply (rule_tac x="[Event e]\<^sub>E # p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event e]\<^sub>E # q''" in exI, simp add: e_in_A)
        apply (rule_tac x="[Event e]\<^sub>E # p''" in bexI, rule_tac x="[Event e]\<^sub>E # q''" in bexI, simp_all add: e_in_A)
        done
    next
      fix p'
      assume e_notin_A: "e \<notin> A"
      assume p_def: "p = [Event e]\<^sub>E # p'"
      assume in_p'_parcomp_q: "\<sigma> @ [[X]\<^sub>R] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
      have 1: "TT {t. [Event e]\<^sub>E # t \<in> P}"
        using TT_P TT_init_event p_P p_def by force
      have 2: "Y \<inter> {ea. ea \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>{t. [Event e]\<^sub>E # t \<in> P}. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma> @ [[ea]\<^sub>E] \<in> x) \<or>
          ea = Tock \<and> (\<exists>x. (\<exists>p\<in>{t. [Event e]\<^sub>E # t \<in> P}. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> x)} = {}"
      proof -
        have "{ea. ea \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>{t. [Event e]\<^sub>E # t \<in> P}. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma> @ [[ea]\<^sub>E] \<in> x) \<or>
            ea = Tock \<and> (\<exists>x. (\<exists>p\<in>{t. [Event e]\<^sub>E # t \<in> P}. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> x)}
          \<subseteq> {ea. ea \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Event e]\<^sub>E # \<sigma> @ [[ea]\<^sub>E] \<in> x) \<or>
                 ea = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Event e]\<^sub>E # \<sigma> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> x)}"
          apply auto
          apply (rule_tac x="[Event e]\<^sub>E # p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" in exI, auto)
          using e_notin_A apply (case_tac q rule:ttWF.cases, auto)
          apply (rule_tac x="[Event e]\<^sub>E # p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" in exI, auto)
          using e_notin_A apply (case_tac q rule:ttWF.cases, auto)
          apply (erule_tac x="[Event e]\<^sub>E # p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" in allE, auto)
          using e_notin_A apply (case_tac q rule:ttWF.cases, auto)
          apply (erule_tac x="[Event e]\<^sub>E # p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" in allE, auto)
          using e_notin_A apply (case_tac q rule:ttWF.cases, auto)
          done
        then show ?thesis
          using disjoint by (smt disjoint_iff_not_equal subset_iff)
      qed
      have 3: "p' \<in> {t. [Event e]\<^sub>E # t \<in> P}"
        using p_P p_def by auto
      have "\<exists>x. (\<exists>p''\<in>{t. [Event e]\<^sub>E # t \<in> P}. \<exists>q''\<in>Q. x = p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'') \<and> \<sigma> @ [[X \<union> Y]\<^sub>R] \<in> x"
        using induction_hypothesis[where P="{t. [Event e]\<^sub>E # t \<in> P}", where Q=Q, where p=p', where q=q, where X=X, where Y=Y]
        using 1 2 3 q_Q in_p'_parcomp_q TT_Q by auto
      then obtain p'' q'' where "p''\<in>{t. [Event e]\<^sub>E # t \<in> P}" "q''\<in>Q" "\<sigma> @ [[X \<union> Y]\<^sub>R] \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q''"
        by auto
      then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Event e]\<^sub>E # \<sigma> @ [[X \<union> Y]\<^sub>R] \<in> x"
        apply (rule_tac x="[Event e]\<^sub>E # p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q''" in exI, cases q'' rule:ttWF.cases, simp_all add: e_notin_A)
        apply (rule_tac x="[Event e]\<^sub>E # p''" in bexI, rule_tac x="q''" in bexI, simp_all add: e_notin_A)+
        done
    next
      fix q'
      assume e_notin_A: "e \<notin> A"
      assume q_def: "q = [Event e]\<^sub>E # q'"
      assume in_p_parcomp_q': "\<sigma> @ [[X]\<^sub>R] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'"
      have 1: "TT {t. [Event e]\<^sub>E # t \<in> Q}"
        using TT_Q TT_init_event q_Q q_def by force
      have 2: "Y \<inter> {ea. ea \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>{t. [Event e]\<^sub>E # t \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma> @ [[ea]\<^sub>E] \<in> x) \<or>
          ea = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>{t. [Event e]\<^sub>E # t \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> x)} = {}"
      proof -
        have "{ea. ea \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>{t. [Event e]\<^sub>E # t \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma> @ [[ea]\<^sub>E] \<in> x) \<or>
            ea = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>{t. [Event e]\<^sub>E # t \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> x)}
          \<subseteq> {ea. ea \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Event e]\<^sub>E # \<sigma> @ [[ea]\<^sub>E] \<in> x) \<or>
                 ea = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Event e]\<^sub>E # \<sigma> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> x)}"
          apply auto
          apply (rule_tac x="p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event e]\<^sub>E # q" in exI, auto)
          using e_notin_A apply (case_tac p rule:ttWF.cases, auto)
          apply (rule_tac x="p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event e]\<^sub>E # q" in exI, auto)
          using e_notin_A apply (case_tac p rule:ttWF.cases, auto)
          apply (erule_tac x="p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event e]\<^sub>E # q" in allE, auto)
          using e_notin_A apply (case_tac p rule:ttWF.cases, auto)
          apply (erule_tac x="p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event e]\<^sub>E # q" in allE, auto)
          using e_notin_A apply (case_tac p rule:ttWF.cases, auto)
          done
        then show ?thesis
          using disjoint by (smt disjoint_iff_not_equal subset_iff)
      qed
      have 3: "q' \<in> {t. [Event e]\<^sub>E # t \<in> Q}"
        using q_Q q_def by auto
      have "\<exists>x. (\<exists>p''\<in>P. \<exists>q''\<in>{t. [Event e]\<^sub>E # t \<in> Q}. x = p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'') \<and> \<sigma> @ [[X \<union> Y]\<^sub>R] \<in> x"
        using induction_hypothesis[where P=P, where Q="{t. [Event e]\<^sub>E # t \<in> Q}", where p=p, where q=q', where X=X, where Y=Y]
        using 1 2 3 p_P in_p_parcomp_q' TT_P by auto
      then obtain p'' q'' where "q''\<in>{t. [Event e]\<^sub>E # t \<in> Q}" "p''\<in>P" "\<sigma> @ [[X \<union> Y]\<^sub>R] \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q''"
        by auto
      then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Event e]\<^sub>E # \<sigma> @ [[X \<union> Y]\<^sub>R] \<in> x"
        apply (rule_tac x="p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event e]\<^sub>E # q''" in exI, cases p'' rule:ttWF.cases, simp_all add: e_notin_A)
        apply (rule_tac x="p''" in bexI, rule_tac x="[Event e]\<^sub>E # q''" in bexI, simp_all add: e_notin_A)+
        done
    qed
  next
    fix P Q :: "'a ttobs list set"
    fix p q \<sigma> :: "'a ttobs list"
    fix X Y Xa :: "'a ttevent set"  
    assume assm1: "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma> @ [[Xa]\<^sub>R] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    then have p_q_cases: "(\<exists> p' q' X1 X2. p = [X1]\<^sub>R # [Tock]\<^sub>E # p' \<and> q = [X2]\<^sub>R # [Tock]\<^sub>E # q' \<and> [[X]\<^sub>R] \<in> ([[X1]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[X2]\<^sub>R]) \<and> \<sigma> @ [[Xa]\<^sub>R] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q') \<or>
      (\<exists> p' X1. p = [X1]\<^sub>R # [Tock]\<^sub>E # p' \<and> q = [[Tick]\<^sub>E] \<and> [[X]\<^sub>R] \<in> ([[X1]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]) \<and> \<sigma> @ [[Xa]\<^sub>R] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]) \<or>
      (\<exists> q' X2. p = [[Tick]\<^sub>E] \<and> q = [X2]\<^sub>R # [Tock]\<^sub>E # q' \<and> [[X]\<^sub>R] \<in> ([[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[X2]\<^sub>R]) \<and> \<sigma> @ [[Xa]\<^sub>R] \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
      by (cases "(p,q)" rule:ttWF2.cases, simp_all)
    assume induction_hypothesis: "(\<And>P Q X Y p q. TT P \<Longrightarrow> TT Q \<Longrightarrow>
      Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma> @ [[e]\<^sub>E] \<in> x) \<or>
        e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> x)} = {} \<Longrightarrow>
      \<sigma> @ [[X]\<^sub>R] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> p \<in> P \<Longrightarrow> q \<in> Q \<Longrightarrow> \<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma> @ [[X \<union> Y]\<^sub>R] \<in> x)"
    assume disjoint: "Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> @ [[e]\<^sub>E] \<in> x) \<or>
                e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)} = {}"
    assume p_P: "p \<in> P" and q_Q: "q \<in> Q"
    assume TT_P: "TT P" and TT_Q: "TT Q"
    show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> @ [[Xa \<union> Y]\<^sub>R] \<in> x"
      using p_q_cases
    proof safe
      fix p' q' X1 X2
      assume p_def: "p = [X1]\<^sub>R # [Tock]\<^sub>E # p'"
      assume q_def: "q = [X2]\<^sub>R # [Tock]\<^sub>E # q'"
      assume refusal_merge: "[[X]\<^sub>R] \<in> [[X1]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[X2]\<^sub>R]"
      assume in_p'_parcomp_q': "\<sigma> @ [[Xa]\<^sub>R] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'"
      have 1: "TT {t. [X1]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
        using TT_P TT_init_tock p_P p_def by blast
      have 2: "TT {t. [X2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}"
        using TT_Q TT_init_tock q_Q q_def by blast
      have 3: "Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>{t. [X1]\<^sub>R # [Tock]\<^sub>E # t \<in> P}. \<exists>q\<in>{t. [X2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma> @ [[e]\<^sub>E] \<in> x) \<or>
        e = Tock \<and> (\<exists>x. (\<exists>p\<in>{t. [X1]\<^sub>R # [Tock]\<^sub>E # t \<in> P}. \<exists>q\<in>{t. [X2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)} = {}"
      proof -
        have "Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>{t. [X1]\<^sub>R # [Tock]\<^sub>E # t \<in> P}. \<exists>q\<in>{t. [X2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma> @ [[e]\<^sub>E] \<in> x) \<or>
            e = Tock \<and> (\<exists>x. (\<exists>p\<in>{t. [X1]\<^sub>R # [Tock]\<^sub>E # t \<in> P}. \<exists>q\<in>{t. [X2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)}
          \<subseteq> Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> @ [[e]\<^sub>E] \<in> x) \<or>
            e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)}"
          apply (auto, insert refusal_merge)
          apply (rule_tac x="[X1]\<^sub>R # [Tock]\<^sub>E # p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [X2]\<^sub>R # [Tock]\<^sub>E # q" in exI, simp)
          apply (rule_tac x="[X1]\<^sub>R # [Tock]\<^sub>E # p" in bexI, rule_tac x="[X2]\<^sub>R # [Tock]\<^sub>E # q" in bexI, simp, blast, blast)
          apply (rule_tac x="[X1]\<^sub>R # [Tock]\<^sub>E # p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [X2]\<^sub>R # [Tock]\<^sub>E # q" in exI, simp)
          apply (rule_tac x="[X1]\<^sub>R # [Tock]\<^sub>E # p" in bexI, rule_tac x="[X2]\<^sub>R # [Tock]\<^sub>E # q" in bexI, simp, blast, blast)
          apply (erule_tac x="[X1]\<^sub>R # [Tock]\<^sub>E # p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [X2]\<^sub>R # [Tock]\<^sub>E # q" in allE, simp, safe)
          apply (erule_tac x="[X1]\<^sub>R # [Tock]\<^sub>E # p" in ballE, erule_tac x="[X2]\<^sub>R # [Tock]\<^sub>E # q" in ballE, simp, blast, blast)
          apply (erule_tac x="[X1]\<^sub>R # [Tock]\<^sub>E # p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [X2]\<^sub>R # [Tock]\<^sub>E # q" in allE, simp, safe)
          apply (erule_tac x="[X1]\<^sub>R # [Tock]\<^sub>E # p" in ballE, erule_tac x="[X2]\<^sub>R # [Tock]\<^sub>E # q" in ballE, simp, blast, blast)
          done
        then show ?thesis
          using disjoint by force
      qed
      have 4: "p' \<in> {t. [X1]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
        using p_P p_def by auto
      have 5: "q' \<in> {t. [X2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}"
        using q_Q q_def by auto
      have "\<exists>x. (\<exists>p\<in>{t. [X1]\<^sub>R # [Tock]\<^sub>E # t \<in> P}. \<exists>q\<in>{t. [X2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma> @ [[Xa \<union> Y]\<^sub>R] \<in> x"
        using induction_hypothesis[where P="{t. [X1]\<^sub>R # [Tock]\<^sub>E # t \<in> P}", where Q="{t. [X2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}", where p=p', where q=q', where X=Xa, where Y=Y]
        using 1 2 3 4 5 in_p'_parcomp_q' by auto
      then obtain p'' q'' where "p''\<in>{t. [X1]\<^sub>R # [Tock]\<^sub>E # t \<in> P}" "q''\<in>{t. [X2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}" "\<sigma> @ [[Xa \<union> Y]\<^sub>R] \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q''"
        by auto
      then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> @ [[Xa \<union> Y]\<^sub>R] \<in> x"
        using refusal_merge
        apply (rule_tac x="[X1]\<^sub>R # [Tock]\<^sub>E # p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [X2]\<^sub>R # [Tock]\<^sub>E # q''" in exI, simp)
        apply (rule_tac x="[X1]\<^sub>R # [Tock]\<^sub>E # p''" in bexI, rule_tac x="[X2]\<^sub>R # [Tock]\<^sub>E # q''" in bexI, simp_all)
        done
    next
      fix p' X1
      assume p_def: "p = [X1]\<^sub>R # [Tock]\<^sub>E # p'"
      assume q_def: "q = [[Tick]\<^sub>E]"
      assume refusal_merge: "[[X]\<^sub>R] \<in> [[X1]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
      assume in_p'_parcomp_Tick: "\<sigma> @ [[Xa]\<^sub>R] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
      have 1: "TT {t. [X1]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
        using TT_P TT_init_tock p_P p_def by blast
      have 2: "TT {[], [[Tick]\<^sub>E]}"
        by (metis TT_Skip SkipTT_def)
      have 3: "Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>{t. [X1]\<^sub>R # [Tock]\<^sub>E # t \<in> P}. \<exists>q\<in>{[], [[Tick]\<^sub>E]}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma> @ [[e]\<^sub>E] \<in> x) \<or>
         e = Tock \<and> (\<exists>x. (\<exists>p\<in>{t. [X1]\<^sub>R # [Tock]\<^sub>E # t \<in> P}. \<exists>q\<in>{[], [[Tick]\<^sub>E]}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)} = {}"
      proof -
        have "Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>{t. [X1]\<^sub>R # [Tock]\<^sub>E # t \<in> P}. \<exists>q\<in>{[], [[Tick]\<^sub>E]}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma> @ [[e]\<^sub>E] \<in> x) \<or>
            e = Tock \<and> (\<exists>x. (\<exists>p\<in>{t. [X1]\<^sub>R # [Tock]\<^sub>E # t \<in> P}. \<exists>q\<in>{[], [[Tick]\<^sub>E]}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)}
          \<subseteq> Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> @ [[e]\<^sub>E] \<in> x) \<or>
            e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)}"
        proof auto
          fix x p
          assume case_assms: "\<sigma> @ [[x]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C []" "[X1]\<^sub>R # [Tock]\<^sub>E # p \<in> P"
          then obtain p' where p'_assms: "\<sigma> @ [[x]\<^sub>E] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" "p' \<lesssim>\<^sub>C p"
            using merge_traces_empty_merge_traces_tick by blast
          then have "[X1]\<^sub>R # [Tock]\<^sub>E # p' \<in> P"
            using TT_P case_assms unfolding TT_def TT1_def apply auto
            by (erule_tac x="[X1]\<^sub>R # [Tock]\<^sub>E # p'" in allE, auto)
          then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> @ [[x]\<^sub>E] \<in> xa"
            using refusal_merge q_def q_Q p'_assms apply (rule_tac x="[X1]\<^sub>R # [Tock]\<^sub>E # p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" in exI, safe, simp_all)
            by (rule_tac x="[X1]\<^sub>R # [Tock]\<^sub>E # p'" in bexI, simp_all, rule_tac x="[[Tick]\<^sub>E]" in bexI, simp_all)
        next
          fix x p
          assume case_assms: "\<sigma> @ [[x]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C []" "[X1]\<^sub>R # [Tock]\<^sub>E # p \<in> P"
          then obtain p' where p'_assms: "\<sigma> @ [[x]\<^sub>E] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" "p' \<lesssim>\<^sub>C p"
            using merge_traces_empty_merge_traces_tick by blast
          then have "[X1]\<^sub>R # [Tock]\<^sub>E # p' \<in> P"
            using TT_P case_assms unfolding TT_def TT1_def apply auto
            by (erule_tac x="[X1]\<^sub>R # [Tock]\<^sub>E # p'" in allE, auto)
          then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> @ [[x]\<^sub>E] \<in> xa"
            using refusal_merge q_def q_Q p'_assms apply (rule_tac x="[X1]\<^sub>R # [Tock]\<^sub>E # p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" in exI, safe, simp_all)
            by (rule_tac x="[X1]\<^sub>R # [Tock]\<^sub>E # p'" in bexI, simp_all, rule_tac x="[[Tick]\<^sub>E]" in bexI, simp_all)
        next
          fix p
          assume case_assms: "\<sigma> @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C []" "[X1]\<^sub>R # [Tock]\<^sub>E # p \<in> P"
          then obtain p' where p'_assms: "\<sigma> @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" "p' \<lesssim>\<^sub>C p"
            using merge_traces_empty_merge_traces_tick by blast
          then have "[X1]\<^sub>R # [Tock]\<^sub>E # p' \<in> P"
            using TT_P case_assms unfolding TT_def TT1_def apply auto
            by (erule_tac x="[X1]\<^sub>R # [Tock]\<^sub>E # p'" in allE, auto)
          then show "\<forall>x. (\<forall>p\<in>P. \<forall>q\<in>Q. x \<noteq> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<or> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<notin> x \<Longrightarrow> False"
            using refusal_merge q_def q_Q p'_assms apply (erule_tac x="[X1]\<^sub>R # [Tock]\<^sub>E # p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" in allE, safe, simp_all)
            by (erule_tac x="[X1]\<^sub>R # [Tock]\<^sub>E # p'" in ballE, simp_all, erule_tac x="[[Tick]\<^sub>E]" in ballE, simp_all)
        next
          fix p
          assume case_assms: "\<sigma> @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C []" "[X1]\<^sub>R # [Tock]\<^sub>E # p \<in> P"
          then obtain p' where p'_assms: "\<sigma> @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" "p' \<lesssim>\<^sub>C p"
            using merge_traces_empty_merge_traces_tick by blast
          then have "[X1]\<^sub>R # [Tock]\<^sub>E # p' \<in> P"
            using TT_P case_assms unfolding TT_def TT1_def apply auto
            by (erule_tac x="[X1]\<^sub>R # [Tock]\<^sub>E # p'" in allE, auto)
          then show "\<forall>x. (\<forall>p\<in>P. \<forall>q\<in>Q. x \<noteq> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<or> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<notin> x \<Longrightarrow>
            \<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> @ [[Tock]\<^sub>E] \<in> x"
            using refusal_merge q_def q_Q p'_assms apply (erule_tac x="[X1]\<^sub>R # [Tock]\<^sub>E # p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" in allE, safe, simp_all)
            by (erule_tac x="[X1]\<^sub>R # [Tock]\<^sub>E # p'" in ballE, simp_all, erule_tac x="[[Tick]\<^sub>E]" in ballE, simp_all)
        next
          fix x p
          assume case_assms: "\<sigma> @ [[x]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" "[X1]\<^sub>R # [Tock]\<^sub>E # p \<in> P"
          then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> @ [[x]\<^sub>E] \<in> xa"
            using refusal_merge q_def q_Q apply (rule_tac x="[X1]\<^sub>R # [Tock]\<^sub>E # p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" in exI, safe, simp_all)
            by (rule_tac x="[X1]\<^sub>R # [Tock]\<^sub>E # p" in bexI, simp_all, rule_tac x="[[Tick]\<^sub>E]" in bexI, simp_all)
        next
          fix x p
          assume case_assms: "\<sigma> @ [[x]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" "[X1]\<^sub>R # [Tock]\<^sub>E # p \<in> P"
          then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> @ [[x]\<^sub>E] \<in> xa"
            using refusal_merge q_def q_Q apply (rule_tac x="[X1]\<^sub>R # [Tock]\<^sub>E # p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" in exI, safe, simp_all)
            by (rule_tac x="[X1]\<^sub>R # [Tock]\<^sub>E # p" in bexI, simp_all, rule_tac x="[[Tick]\<^sub>E]" in bexI, simp_all)
        next
          fix p
          assume case_assms: "\<sigma> @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" "[X1]\<^sub>R # [Tock]\<^sub>E # p \<in> P"
          then show "\<forall>x. (\<forall>p\<in>P. \<forall>q\<in>Q. x \<noteq> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<or> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<notin> x \<Longrightarrow> False"
            using refusal_merge q_def q_Q apply (erule_tac x="[X1]\<^sub>R # [Tock]\<^sub>E # p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" in allE, safe, simp_all)
            by (erule_tac x="[X1]\<^sub>R # [Tock]\<^sub>E # p" in ballE, simp_all, erule_tac x="[[Tick]\<^sub>E]" in ballE, simp_all)
        next
          fix p
          assume case_assms: "\<sigma> @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" "[X1]\<^sub>R # [Tock]\<^sub>E # p \<in> P"
          then show "\<forall>x. (\<forall>p\<in>P. \<forall>q\<in>Q. x \<noteq> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<or> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<notin> x \<Longrightarrow>
            \<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> @ [[Tock]\<^sub>E] \<in> x"
            using refusal_merge q_def q_Q apply (erule_tac x="[X1]\<^sub>R # [Tock]\<^sub>E # p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" in allE, safe, simp_all)
            by (erule_tac x="[X1]\<^sub>R # [Tock]\<^sub>E # p" in ballE, simp_all, erule_tac x="[[Tick]\<^sub>E]" in ballE, simp_all)
        qed
        then show ?thesis
          using disjoint by auto
      qed
      have 4: "p' \<in> {t. [X1]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
        using p_P p_def by blast
      have "\<exists>x. (\<exists>p\<in>{t. [X1]\<^sub>R # [Tock]\<^sub>E # t \<in> P}. \<exists>q\<in>{[], [[Tick]\<^sub>E]}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma> @ [[Xa \<union> Y]\<^sub>R] \<in> x"
        using induction_hypothesis[where P="{t. [X1]\<^sub>R # [Tock]\<^sub>E # t \<in> P}", where Q="{[], [[Tick]\<^sub>E]}", where p=p', where q="[[Tick]\<^sub>E]", where X=Xa, where Y=Y]
        using 1 2 3 4 in_p'_parcomp_Tick by auto
      then obtain p'' where "p''\<in>{t. [X1]\<^sub>R # [Tock]\<^sub>E # t \<in> P}" "\<sigma> @ [[Xa \<union> Y]\<^sub>R] \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
      proof auto
        fix p
        assume assm1: "\<And>p''. [X1]\<^sub>R # [Tock]\<^sub>E # p'' \<in> P \<Longrightarrow> \<sigma> @ [[Xa \<union> Y]\<^sub>R] \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E] \<Longrightarrow> thesis"
        assume assm2: "\<sigma> @ [[Xa \<union> Y]\<^sub>R] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C []"
        assume assm3: "[X1]\<^sub>R # [Tock]\<^sub>E # p \<in> P"
        obtain p' where "p' \<lesssim>\<^sub>C p" "\<sigma> @ [[Xa \<union> Y]\<^sub>R] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
          using merge_traces_empty_merge_traces_tick[where r="\<sigma> @ [[Xa \<union> Y]\<^sub>R]", where s=p] assm2 by auto
        also then have "[X1]\<^sub>R # [Tock]\<^sub>E # p' \<in> P"
          using TT_P assm3 unfolding TT_def TT1_def apply auto
          by (erule_tac x="[X1]\<^sub>R # [Tock]\<^sub>E # p'" in allE, auto)
        then show "thesis"
          using assm1 calculation by blast
      qed
      then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> @ [[Xa \<union> Y]\<^sub>R] \<in> x"
        using refusal_merge q_Q q_def
        apply (rule_tac x="[X1]\<^sub>R # [Tock]\<^sub>E # p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" in exI, simp_all)
        apply (rule_tac x="[X1]\<^sub>R # [Tock]\<^sub>E # p''" in bexI, simp_all)
        apply (rule_tac x="[[Tick]\<^sub>E]" in bexI, simp_all)
        done
    next
      fix q' X2
      assume p_def: "p = [[Tick]\<^sub>E]"
      assume q_def: "q = [X2]\<^sub>R # [Tock]\<^sub>E # q'"
      assume refusal_merge: "[[X]\<^sub>R] \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[X2]\<^sub>R]"
      assume in_Tick_parcomp_q': "\<sigma> @ [[Xa]\<^sub>R] \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'"
      have 1: "TT {t. [X2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}"
        using TT_Q TT_init_tock q_Q q_def by blast
      have 2: "TT {[], [[Tick]\<^sub>E]}"
        by (metis TT_Skip SkipTT_def)
      have 3: "Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>{[], [[Tick]\<^sub>E]}. \<exists>q\<in>{t. [X2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma> @ [[e]\<^sub>E] \<in> x) \<or>
         e = Tock \<and> (\<exists>x. (\<exists>p\<in>{[], [[Tick]\<^sub>E]}. \<exists>q\<in>{t. [X2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)} = {}"
      proof -
        have "Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>{[], [[Tick]\<^sub>E]}. \<exists>q\<in>{t. [X2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma> @ [[e]\<^sub>E] \<in> x) \<or>
            e = Tock \<and> (\<exists>x. (\<exists>p\<in>{[], [[Tick]\<^sub>E]}. \<exists>q\<in>{t. [X2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)}
          \<subseteq> Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> @ [[e]\<^sub>E] \<in> x) \<or>
            e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)}"
        proof auto
          fix x q
          assume case_assms: "\<sigma> @ [[x]\<^sub>E] \<in> [] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "[X2]\<^sub>R # [Tock]\<^sub>E # q \<in> Q"
          then obtain q' where q'_assms: "\<sigma> @ [[x]\<^sub>E] \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'" "q' \<lesssim>\<^sub>C q"
            using merge_traces_empty_merge_traces_tick merge_traces_comm by blast
          then have "[X2]\<^sub>R # [Tock]\<^sub>E # q' \<in> Q"
            using TT_Q case_assms unfolding TT_def TT1_def apply auto
            by (erule_tac x="[X2]\<^sub>R # [Tock]\<^sub>E # q'" in allE, auto)
          then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> @ [[x]\<^sub>E] \<in> xa"
            using refusal_merge p_def p_P q'_assms apply (rule_tac x="[[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [X2]\<^sub>R # [Tock]\<^sub>E # q'" in exI, safe, simp_all)
            by (rule_tac x="[[Tick]\<^sub>E]" in bexI, simp_all, rule_tac x="[X2]\<^sub>R # [Tock]\<^sub>E # q'" in bexI, simp_all)
        next
          fix x q
          assume case_assms: "\<sigma> @ [[x]\<^sub>E] \<in> [] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "[X2]\<^sub>R # [Tock]\<^sub>E # q \<in> Q"
          then obtain q' where q'_assms: "\<sigma> @ [[x]\<^sub>E] \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'" "q' \<lesssim>\<^sub>C q"
            using merge_traces_empty_merge_traces_tick merge_traces_comm by blast
          then have "[X2]\<^sub>R # [Tock]\<^sub>E # q' \<in> Q"
            using TT_Q case_assms unfolding TT_def TT1_def apply auto
            by (erule_tac x="[X2]\<^sub>R # [Tock]\<^sub>E # q'" in allE, auto)
          then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> @ [[x]\<^sub>E] \<in> xa"
            using refusal_merge p_def p_P q'_assms apply (rule_tac x="[[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [X2]\<^sub>R # [Tock]\<^sub>E # q'" in exI, safe, simp_all)
            by (rule_tac x="[[Tick]\<^sub>E]" in bexI, simp_all, rule_tac x="[X2]\<^sub>R # [Tock]\<^sub>E # q'" in bexI, simp_all)
        next
          fix q
          assume case_assms: "\<sigma> @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<in> [] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "[X2]\<^sub>R # [Tock]\<^sub>E # q \<in> Q"
          then obtain q' where q'_assms: "\<sigma> @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'" "q' \<lesssim>\<^sub>C q"
            using merge_traces_empty_merge_traces_tick merge_traces_comm  by blast
          then have "[X2]\<^sub>R # [Tock]\<^sub>E # q' \<in> Q"
            using TT_Q case_assms unfolding TT_def TT1_def apply auto
            by (erule_tac x="[X2]\<^sub>R # [Tock]\<^sub>E # q'" in allE, auto)
          then show "\<forall>x. (\<forall>p\<in>P. \<forall>q\<in>Q. x \<noteq> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<or> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<notin> x \<Longrightarrow> False"
            using refusal_merge p_def p_P q'_assms apply (erule_tac x="[[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [X2]\<^sub>R # [Tock]\<^sub>E # q'" in allE, safe, simp_all)
            by (erule_tac x="[[Tick]\<^sub>E]" in ballE, simp_all, erule_tac x="[X2]\<^sub>R # [Tock]\<^sub>E # q'" in ballE, simp_all)
        next
          fix q
          assume case_assms: "\<sigma> @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<in> [] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "[X2]\<^sub>R # [Tock]\<^sub>E # q \<in> Q"
          then obtain q' where q'_assms: "\<sigma> @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'" "q' \<lesssim>\<^sub>C q"
            using merge_traces_empty_merge_traces_tick merge_traces_comm  by blast
          then have "[X2]\<^sub>R # [Tock]\<^sub>E # q' \<in> Q"
            using TT_Q case_assms unfolding TT_def TT1_def apply auto
            by (erule_tac x="[X2]\<^sub>R # [Tock]\<^sub>E # q'" in allE, auto)
          then show "\<forall>x. (\<forall>p\<in>P. \<forall>q\<in>Q. x \<noteq> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<or> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<notin> x \<Longrightarrow>
            \<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> @ [[Tock]\<^sub>E] \<in> x"
            using refusal_merge p_def p_P q'_assms apply (erule_tac x="[[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [X2]\<^sub>R # [Tock]\<^sub>E # q'" in allE, safe, simp_all)
            by (erule_tac x="[[Tick]\<^sub>E]" in ballE, simp_all, erule_tac x="[X2]\<^sub>R # [Tock]\<^sub>E # q'" in ballE, simp_all)
        next
          fix x q
          assume case_assms: "\<sigma> @ [[x]\<^sub>E] \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "[X2]\<^sub>R # [Tock]\<^sub>E # q \<in> Q"
          then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> @ [[x]\<^sub>E] \<in> xa"
            using refusal_merge p_def p_P apply (rule_tac x="[[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [X2]\<^sub>R # [Tock]\<^sub>E # q" in exI, safe, simp_all)
            by (rule_tac x="[[Tick]\<^sub>E]" in bexI, simp_all, rule_tac x="[X2]\<^sub>R # [Tock]\<^sub>E # q" in bexI, simp_all)
        next
          fix x q
          assume case_assms: "\<sigma> @ [[x]\<^sub>E] \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "[X2]\<^sub>R # [Tock]\<^sub>E # q \<in> Q"
          then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> @ [[x]\<^sub>E] \<in> xa"
            using refusal_merge p_def p_P apply (rule_tac x="[[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [X2]\<^sub>R # [Tock]\<^sub>E # q" in exI, safe, simp_all)
            by (rule_tac x="[[Tick]\<^sub>E]" in bexI, simp_all, rule_tac x="[X2]\<^sub>R # [Tock]\<^sub>E # q" in bexI, simp_all)
        next
          fix q
          assume case_assms: "\<sigma> @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "[X2]\<^sub>R # [Tock]\<^sub>E # q \<in> Q"
          then show "\<forall>x. (\<forall>p\<in>P. \<forall>q\<in>Q. x \<noteq> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<or> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<notin> x \<Longrightarrow> False"
            using refusal_merge p_def p_P apply (erule_tac x="[[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [X2]\<^sub>R # [Tock]\<^sub>E # q" in allE, safe, simp_all)
            by (erule_tac x="[[Tick]\<^sub>E]" in ballE, simp_all, erule_tac x="[X2]\<^sub>R # [Tock]\<^sub>E # q" in ballE, simp_all)
        next
          fix q
          assume case_assms: "\<sigma> @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "[X2]\<^sub>R # [Tock]\<^sub>E # q \<in> Q"
          then show "\<forall>x. (\<forall>p\<in>P. \<forall>q\<in>Q. x \<noteq> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<or> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<notin> x \<Longrightarrow>
            \<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> @ [[Tock]\<^sub>E] \<in> x"
            using refusal_merge p_def p_P apply (erule_tac x="[[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [X2]\<^sub>R # [Tock]\<^sub>E # q" in allE, safe, simp_all)
            by (erule_tac x="[[Tick]\<^sub>E]" in ballE, simp_all, erule_tac x="[X2]\<^sub>R # [Tock]\<^sub>E # q" in ballE, simp_all)
        qed
        then show ?thesis
          using disjoint by auto
      qed
      have 4: "q' \<in> {t. [X2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}"
        using q_Q q_def by blast
      have "\<exists>x. (\<exists>p\<in>{[], [[Tick]\<^sub>E]}. \<exists>q\<in>{t. [X2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma> @ [[Xa \<union> Y]\<^sub>R] \<in> x"
        using induction_hypothesis[where P="{[], [[Tick]\<^sub>E]}", where Q="{t. [X2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}", where p="[[Tick]\<^sub>E]", where q=q', where X=Xa, where Y=Y]
        using 1 2 3 4 in_Tick_parcomp_q' by auto
      then obtain q'' where "q''\<in>{t. [X2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}" "\<sigma> @ [[Xa \<union> Y]\<^sub>R] \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q''"
      proof auto
        fix q
        assume assm1: "\<And>q''. [X2]\<^sub>R # [Tock]\<^sub>E # q'' \<in> Q \<Longrightarrow> \<sigma> @ [[Xa \<union> Y]\<^sub>R] \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'' \<Longrightarrow> thesis"
        assume assm2: "\<sigma> @ [[Xa \<union> Y]\<^sub>R] \<in> [] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
        assume assm3: "[X2]\<^sub>R # [Tock]\<^sub>E # q \<in> Q"
        obtain q' where "q' \<lesssim>\<^sub>C q" "\<sigma> @ [[Xa \<union> Y]\<^sub>R] \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'"
          using merge_traces_empty_merge_traces_tick[where r="\<sigma> @ [[Xa \<union> Y]\<^sub>R]", where s=q] merge_traces_comm assm2 by blast
        also then have "[X2]\<^sub>R # [Tock]\<^sub>E # q' \<in> Q"
          using TT_Q assm3 unfolding TT_def TT1_def apply auto
          by (erule_tac x="[X2]\<^sub>R # [Tock]\<^sub>E # q'" in allE, auto)
        then show "thesis"
          using assm1 calculation by blast
      qed
      then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> @ [[Xa \<union> Y]\<^sub>R] \<in> x"
        using refusal_merge p_P p_def
        apply (rule_tac x="[[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [X2]\<^sub>R # [Tock]\<^sub>E # q''" in exI, simp_all)
        apply (rule_tac x="[[Tick]\<^sub>E]" in bexI, simp_all)
        apply (rule_tac x="[X2]\<^sub>R # [Tock]\<^sub>E # q''" in bexI, simp_all)
        done
    qed
  next
    fix va P Q X Y p q
    assume "[Tock]\<^sub>E # va @ [[X]\<^sub>R] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "p \<in> P" "q \<in> Q" "TT P" "TT Q"
    then have "ttWF ([Tock]\<^sub>E # va @ [[X]\<^sub>R])"
      using TT_wf merge_traces_wf by blast
    then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Tock]\<^sub>E # va @ [[X \<union> Y]\<^sub>R] \<in> x"
      by simp
  next
    fix v vc P Q X Y p q
    assume "[Tock]\<^sub>E # v # vc @ [[X]\<^sub>R] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "p \<in> P" "q \<in> Q" "TT P" "TT Q"
    then have "ttWF ([Tock]\<^sub>E # v # vc @ [[X]\<^sub>R])"
      using TT_wf merge_traces_wf by blast
    then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Tock]\<^sub>E # v # vc @ [[X \<union> Y]\<^sub>R] \<in> x"
      by simp
  next
    fix v vc P Q X Y p q
    assume "[Tick]\<^sub>E # v # vc @ [[X]\<^sub>R] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "p \<in> P" "q \<in> Q" "TT P" "TT Q"
    then have "ttWF ([Tick]\<^sub>E # v # vc @ [[X]\<^sub>R])"
      using TT_wf merge_traces_wf by blast
    then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Tick]\<^sub>E # v # vc @ [[X \<union> Y]\<^sub>R] \<in> x"
      by simp
  next
    fix vb vc P Q X Y p q
    assume "[Tock]\<^sub>E # vb # vc @ [[X]\<^sub>R] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "p \<in> P" "q \<in> Q" "TT P" "TT Q"
    then have "ttWF ([Tock]\<^sub>E # vb # vc @ [[X]\<^sub>R])"
      using TT_wf merge_traces_wf by blast
    then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Tock]\<^sub>E # vb # vc @ [[X \<union> Y]\<^sub>R] \<in> x"
      by simp
  next
    fix vb vc P Q X Y p q
    assume "[Tick]\<^sub>E # vb # vc @ [[X]\<^sub>R] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "p \<in> P" "q \<in> Q" "TT P" "TT Q"
    then have "ttWF ([Tick]\<^sub>E # vb # vc @ [[X]\<^sub>R])"
      using TT_wf merge_traces_wf by blast
    then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Tick]\<^sub>E # vb # vc @ [[X \<union> Y]\<^sub>R] \<in> x"
      by simp
  next
    fix va vd vc P Q X Y p q
    assume "[va]\<^sub>R # [Event vd]\<^sub>E # vc @ [[X]\<^sub>R] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "p \<in> P" "q \<in> Q" "TT P" "TT Q"
    then have "ttWF ([va]\<^sub>R # [Event vd]\<^sub>E # vc @ [[X]\<^sub>R])"
      using TT_wf merge_traces_wf by blast
    then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [va]\<^sub>R # [Event vd]\<^sub>E # vc @ [[X \<union> Y]\<^sub>R] \<in> x"
      by simp
  next
    fix va vc P Q X Y p q
    assume "[va]\<^sub>R # [Tick]\<^sub>E # vc @ [[X]\<^sub>R] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "p \<in> P" "q \<in> Q" "TT P" "TT Q"
    then have "ttWF ([va]\<^sub>R # [Tick]\<^sub>E # vc @ [[X]\<^sub>R])"
      using TT_wf merge_traces_wf by blast
    then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [va]\<^sub>R # [Tick]\<^sub>E # vc @ [[X \<union> Y]\<^sub>R] \<in> x"
      by simp
  next
    fix va v vc P Q X Y p q
    assume "[va]\<^sub>R # [v]\<^sub>R # vc @ [[X]\<^sub>R] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "p \<in> P" "q \<in> Q" "TT P" "TT Q"
    then have "ttWF ([va]\<^sub>R # [v]\<^sub>R # vc @ [[X]\<^sub>R])"
      using TT_wf merge_traces_wf by blast
    then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [va]\<^sub>R # [v]\<^sub>R # vc @ [[X \<union> Y]\<^sub>R] \<in> x"
      by simp
  qed
qed   

lemma TT2_ParComp:
  assumes "TT P" "TT Q" "TT2 P" "TT2 Q"
  shows "TT2 (P \<lbrakk>A\<rbrakk>\<^sub>C Q)"
  unfolding TT2_def ParCompTT_def
proof (auto)
  fix \<rho> \<sigma>
  have "\<And>P Q X Y p q. TT P \<Longrightarrow> TT Q \<Longrightarrow> TT2 P \<Longrightarrow> TT2 Q \<Longrightarrow>
    Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<rho> @ [[e]\<^sub>E] \<in> x) \<or>
      e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> x)} = {} \<Longrightarrow>
    \<rho> @ [X]\<^sub>R # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> p \<in> P \<Longrightarrow> q \<in> Q \<Longrightarrow> \<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> x"
  proof (induct \<rho> rule:ttWF.induct, auto)
    fix P Q :: "'a ttobs list set"
    fix X Y :: "'a ttevent set"
    fix p q :: "'a ttobs list"
    assume TT_P: "TT P" and TT_Q: "TT Q"
    assume TT2_P: "TT2 P" and TT2_Q: "TT2 Q"
    assume assm1: "Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[e]\<^sub>E] \<in> x) \<or>
                e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> x)} = {}"
    assume assm2: "[X]\<^sub>R # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    assume p_in_P: "p \<in> P" and q_in_Q: "q \<in> Q"
    have "ttWF p \<and> ttWF q"
      using TT_P TT_Q TT_wf p_in_P q_in_Q by blast
    then have "ttWF ([X]\<^sub>R # \<sigma>)"
      using assm2 merge_traces_wf by blast
    then have "\<sigma> = [] \<or> (\<exists> \<sigma>'. \<sigma> = [Tock]\<^sub>E # \<sigma>')"
      using assm2 by (cases \<sigma> rule:ttWF.cases, auto)
    then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X \<union> Y]\<^sub>R # \<sigma> \<in> x"
    proof auto
      assume case_assm: "\<sigma> = []"
      have "TT2w (P \<lbrakk>A\<rbrakk>\<^sub>C Q)"
        by (simp add: TT2w_ParComp TT_P TT_Q)
      then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X \<union> Y]\<^sub>R] \<in> x"
        using case_assm assm1 assm2 p_in_P q_in_Q unfolding TT2w_def ParCompTT_def apply auto
        by (erule_tac x="[]" in allE, erule_tac x="X" in allE, erule_tac x="Y" in allE, auto, fastforce)
    next
      fix \<sigma>'
      assume case_assm: "\<sigma> = [Tock]\<^sub>E # \<sigma>'"
      then have p_q_cases: "(\<exists> p' q' X1 X2. p = [X1]\<^sub>R # [Tock]\<^sub>E # p' \<and> q = [X2]\<^sub>R # [Tock]\<^sub>E # q' \<and> [[X]\<^sub>R] \<in> ([[X1]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[X2]\<^sub>R]) \<and> \<sigma>' \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q') \<or>
      (\<exists> p' X1. p = [X1]\<^sub>R # [Tock]\<^sub>E # p' \<and> q = [[Tick]\<^sub>E] \<and> [[X]\<^sub>R] \<in> ([[X1]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]) \<and> \<sigma>' \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]) \<or>
      (\<exists> q' X2. p = [[Tick]\<^sub>E] \<and> q = [X2]\<^sub>R # [Tock]\<^sub>E # q' \<and> [[X]\<^sub>R] \<in> ([[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[X2]\<^sub>R]) \<and> \<sigma>' \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
        using assm2 case_assm by (cases "(p,q)" rule:ttWF2.cases, simp_all)
      have set1: "{e. \<exists> ea. e = Event ea \<and> ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> P} \<union> {e. \<exists> ea. e = Event ea \<and> ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> Q}
        \<subseteq> {e. \<exists> ea. e = Event ea \<and> ea \<notin> A \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[Event ea]\<^sub>E] \<in> x)}"
      proof auto
        fix x
        assume "[[Event x]\<^sub>E] \<in> P" "x \<notin> A"
        also have "[] \<in> Q"
          by (simp add: TT_empty TT_Q)
        then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[Event x]\<^sub>E] \<in> xa"
          using calculation apply (rule_tac x="[[Event x]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C []" in exI, auto)
          apply (rule_tac x="[[Event x]\<^sub>E]" in bexI, auto)
          apply (rule_tac x="[]" in bexI, auto)
          done
      next
        fix x
        assume "[[Event x]\<^sub>E] \<in> Q" "x \<notin> A"
        also have "[] \<in> P"
          by (simp add: TT_empty TT_P)
        then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[Event x]\<^sub>E] \<in> xa"
          using calculation apply (rule_tac x="[] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Event x]\<^sub>E]" in exI, auto)
          apply (rule_tac x="[]" in bexI, auto)
          apply (rule_tac x="[[Event x]\<^sub>E]" in bexI, auto)
          done
      qed
      have set2: "{Event ea |ea. ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> P} \<inter> {Event ea |ea. ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> Q}
        \<subseteq> {Event ea |ea. ea \<in> A \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[Event ea]\<^sub>E] \<in> x)}"
        apply (auto, rule_tac x="[[Event eaa]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Event eaa]\<^sub>E]" in exI, auto)
        by (rule_tac x="[[Event eaa]\<^sub>E]" in bexI, auto, rule_tac x="[[Event eaa]\<^sub>E]" in bexI, auto)

      have set2: "{Event ea |ea. ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> P} \<inter> {Event ea |ea. ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> Q}
        \<subseteq> {Event ea |ea. ea \<in> A \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[Event ea]\<^sub>E] \<in> x)}"
        apply (auto, rule_tac x="[[Event eaa]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Event eaa]\<^sub>E]" in exI, auto)
        by (rule_tac x="[[Event eaa]\<^sub>E]" in bexI, auto, rule_tac x="[[Event eaa]\<^sub>E]" in bexI, auto)

      have set2: "{Event ea |ea. ea \<in> A \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[Event ea]\<^sub>E] \<in> x)}
        \<subseteq> {Event ea |ea. ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> P} \<inter> {Event ea |ea. ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> P}"
      proof (auto, case_tac "(p,q)" rule:ttWF2.cases, auto)
        fix \<rho> f \<sigma>
        assume "[Event f]\<^sub>E # \<rho> \<in> P"
        also have "TT1 P"
          using TT_P TT_def by blast
        then show "[[Event f]\<^sub>E] \<in> P"
          using calculation unfolding TT1_def apply auto
          by (erule_tac x="[[Event f]\<^sub>E]" in allE, auto)
      qed
      have set3: "{e. e = Tick \<and> [[Tick]\<^sub>E] \<in> P} \<inter> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> Q} \<subseteq> {e. e = Tick \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[Tick]\<^sub>E] \<in> x)}"
      proof auto
        fix x
        assume "[[Tick]\<^sub>E] \<in> P" "[[Tick]\<^sub>E] \<in> Q"
        then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[Tick]\<^sub>E] \<in> xa"
          apply (rule_tac x="[[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" in exI, auto)
          apply (rule_tac x="[[Tick]\<^sub>E]" in bexI, auto)+
          done
      qed
      have set4: "{e. e = Tock \<and> [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P} \<inter> {e. e = Tock \<and> [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q} \<subseteq> {e. e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X]\<^sub>R, [Tock]\<^sub>E] \<in> x)}"
      proof auto
        fix x
        assume "[[X]\<^sub>R, [Tock]\<^sub>E] \<in> P" "[[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
        then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X]\<^sub>R, [Tock]\<^sub>E] \<in> x"
          apply (rule_tac x="[[X]\<^sub>R, [Tock]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[X]\<^sub>R, [Tock]\<^sub>E]" in exI, auto)
          apply (rule_tac x="[[X]\<^sub>R, [Tock]\<^sub>E]" in bexI, auto)+
          done
      qed
      have "\<exists> B C. Y \<inter> (Event ` A \<union> {Tick}) = B \<union> C
          \<and> B \<inter> ({e. \<exists> ea. e = Event ea \<and> ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> P} \<union> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> P}) = {}
          \<and> C \<inter> ({e. \<exists> ea. e = Event ea \<and> ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> Q} \<union> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> Q}) = {}"
      proof -
        have 1: "(Y \<inter> (Event ` A \<union> {Tick})) \<inter> ({e. \<exists> ea. e = Event ea \<and> ea \<in> A \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[Event ea]\<^sub>E] \<in> x)} \<union> {e. e = Tick \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[Tick]\<^sub>E] \<in> x)}) = {}"
          using assm1 by blast
        have 2: "(Y \<inter> (Event ` A \<union> {Tick})) \<inter> ({e. \<exists> ea. e = Event ea \<and> ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> P} \<union> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> P}) \<inter> ({e. \<exists> ea. e = Event ea \<and> ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> Q} \<union> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> Q})
          \<subseteq> (Y \<inter> (Event ` A \<union> {Tick})) \<inter> ({e. \<exists> ea. e = Event ea \<and> ea \<in> A \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[Event ea]\<^sub>E] \<in> x)} \<union> {e. e = Tick \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[Tick]\<^sub>E] \<in> x)})"
          apply auto
          using merge_traces.simps(13) apply blast
          using set2 apply force
          apply (subgoal_tac "False", auto)
          using set2 apply force
          done
        have "(Y \<inter> (Event ` A \<union> {Tick})) \<inter> ({e. \<exists> ea. e = Event ea \<and> ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> P} \<union> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> P}) \<inter> ({e. \<exists> ea. e = Event ea \<and> ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> Q} \<union> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> Q}) \<subseteq> {}"
          using "1" apply simp
          using "2" by auto
        then have "(Y \<inter> (Event ` A \<union> {Tick})) \<inter> ({e. \<exists> ea. e = Event ea \<and> ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> P} \<union> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> P}) \<inter> ({e. \<exists> ea. e = Event ea \<and> ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> Q} \<union> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> Q}) = {}"
          by auto

        then have "\<forall>x\<in>Y \<inter> (Event ` A \<union> {Tick}). x \<notin> ({e. \<exists> ea. e = Event ea \<and> ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> P} \<union> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> P}) \<inter> ({e. \<exists> ea. e = Event ea \<and> ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> Q} \<union> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> Q})"
          by auto
        then have "\<forall>x\<in>Y \<inter> (Event ` A \<union> {Tick}). x \<notin> ({e. \<exists> ea. e = Event ea \<and> ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> P} \<union> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> P}) \<or> x \<notin> ({e. \<exists> ea. e = Event ea \<and> ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> Q} \<union> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> Q})"
          by auto
        then show ?thesis
          apply (rule_tac x="{x\<in>Y \<inter> (Event ` A \<union> {Tick}). x \<notin> ({e. \<exists> ea. e = Event ea \<and> ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> P} \<union> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> P})}" in exI)
          apply (rule_tac x="{x\<in>Y \<inter> (Event ` A \<union> {Tick}). x \<notin> ({e. \<exists> ea. e = Event ea \<and> ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> Q} \<union> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> Q})}" in exI)
          by auto
      qed
      then obtain B C where nontock_sets: "Y \<inter> (Event ` A \<union> {Tick}) = B \<union> C
          \<and> B \<inter> ({e. \<exists> ea. e = Event ea \<and> ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> P} \<union> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> P}) = {}
          \<and> C \<inter> ({e. \<exists> ea. e = Event ea \<and> ea \<in> A \<and> [[Event ea]\<^sub>E] \<in> Q} \<union> {e. e = Tick \<and> [[Tick]\<^sub>E] \<in> Q}) = {}"
        by force

      have nontock_P_assm1: "B \<inter> {e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> P} = {}"
        apply (auto, case_tac x, auto)
        apply (case_tac "x1 \<in> A")
        using set1 nontock_sets by auto
      have nontock_Q_assm1: "C \<inter> {e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> Q} = {}"
        apply (auto, case_tac x, auto)
        apply (case_tac "x1 \<in> A")
        using set1 nontock_sets by auto
      show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<in> x"
        using p_q_cases
      proof (safe, simp_all, safe)
        fix p' q' X1 X2
        assume case_assms2: "q = [X2]\<^sub>R # [Tock]\<^sub>E # q'" "\<sigma>' \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'" "p = [X1]\<^sub>R # [Tock]\<^sub>E # p'" "[[X]\<^sub>R] \<in> [[X1]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[X2]\<^sub>R]"
        have 1: "[[X1]\<^sub>R, [Tock]\<^sub>E] \<in> P"
          using TT_P TT_empty TT_init_tock case_assms2(3) p_in_P by blast
        have 2: "[[X2]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
          using TT_Q TT_empty TT_init_tock case_assms2(1) q_in_Q by blast
        have 3: "B \<inter> {e. (e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> [[X1]\<^sub>R, [e]\<^sub>E] \<in> P)} = {}"
          using nontock_P_assm1 nontock_sets by auto
        have 4: "C \<inter> {e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> [[X2]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
          using nontock_Q_assm1 nontock_sets by auto
        have 5: "{Event e |e. Event e \<in> Y \<and> e \<notin> A} \<inter> {Event e |e. e \<notin> A \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[Event e]\<^sub>E] \<in> x)} = {}"
          using assm1 bex_empty disjoint_iff_not_equal by blast
        have 6: "{Event e |e. Event e \<in> Y \<and> e \<notin> A} \<inter> ({Event ea |ea. ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> P} \<union> {Event ea |ea. ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> Q}) = {}"
          by (smt "5" disjoint_iff_not_equal set1 subsetCE)
        have 7: "(B \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A}) \<inter> {e. (e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> [[X1]\<^sub>R, [e]\<^sub>E] \<in> P)} = {}"
          using 3 6 by blast
        have 8: "(C \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A}) \<inter> {e. (e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> Q) \<or> (e = Tock \<and> [[X2]\<^sub>R, [e]\<^sub>E] \<in> Q)} = {}"
          using 4 6 by blast
        have 9: "[X1 \<union> B \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A}]\<^sub>R # [Tock]\<^sub>E # p' \<in> P"
          using TT2_P 7 case_assms2 p_in_P unfolding TT2_def
          apply (erule_tac x="[]" in allE, erule_tac x="[Tock]\<^sub>E # p'" in allE, erule_tac x="X1" in allE)
          by (erule_tac x="B \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A}" in allE, simp add: sup_assoc)
        have 10: "[X2 \<union> C \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A}]\<^sub>R # [Tock]\<^sub>E # q' \<in> Q"
          using TT2_Q 8 case_assms2 q_in_Q unfolding TT2_def
          apply (erule_tac x="[]" in allE, erule_tac x="[Tock]\<^sub>E # q'" in allE, erule_tac x="X2" in allE)
          by (erule_tac x="C \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A}" in allE, simp add: sup_assoc)
        have 11: "X \<subseteq> X1 \<union> X2"
          using case_assms2(4) by auto
        have 12: "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<in> P \<lbrakk>A\<rbrakk>\<^sub>C Q"
          using assm2 case_assm p_in_P q_in_Q unfolding ParCompTT_def by auto
        have TT1_ParComp: "TT1 (P \<lbrakk>A\<rbrakk>\<^sub>C Q)"
          by (simp add: TT1_ParComp TT_P TT_Q)
        have 13: "[[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<lbrakk>A\<rbrakk>\<^sub>C Q"
          using 12 TT1_ParComp unfolding TT1_def apply (auto) by (erule_tac x="[[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto)
        have 14: "Tock \<in> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[e]\<^sub>E] \<in> x) \<or> e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> x)}"
          using 13 unfolding ParCompTT_def by auto
        have 15: "Tock \<notin> Y"
          using 14 assm1 by auto
        have 16: "Y \<subseteq> B \<union> C \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A}"
          using nontock_sets 15 by (auto, case_tac x, auto)
        have 17: "X \<subseteq> X1 \<union> B \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A} \<union> (X2 \<union> C \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A})"
          using 11 by auto
        have 18: "Y \<subseteq> X1 \<union> B \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A} \<union> (X2 \<union> C \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A})"
          using 16 by auto
        show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<in> x"
          apply (rule_tac x="([X1 \<union> B \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A}]\<^sub>R # [Tock]\<^sub>E # p') \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([X2 \<union> C \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A}]\<^sub>R # [Tock]\<^sub>E # q')" in exI)
          apply safe
          apply (rule_tac x="([X1 \<union> B \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A}]\<^sub>R # [Tock]\<^sub>E # p')" in bexI)
          apply (rule_tac x="([X2 \<union> C \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A}]\<^sub>R # [Tock]\<^sub>E # q')" in bexI, simp_all)
          apply (simp_all add: 9 10 17 18 case_assms2)
        proof -
          have "{e. (e \<in> X2 \<or> e \<in> C \<or> (\<exists>ea. e = Event ea \<and> Event ea \<in> Y \<and> ea \<notin> A)) \<and> e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A}
            = {e \<in> X2. e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A} \<union> {e \<in> C. e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A}
              \<union> {e. (\<exists>ea. e = Event ea \<and> Event ea \<in> Y \<and> ea \<notin> A) \<and> e \<noteq> Tick \<and> e \<notin> Event ` A}"
            by blast
          also have "... = {e \<in> X1. e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A} \<union> {e \<in> C. e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A}
              \<union> {e. (\<exists>ea. e = Event ea \<and> Event ea \<in> Y \<and> ea \<notin> A) \<and> e \<noteq> Tick \<and> e \<notin> Event ` A}"
            using case_assms2(4) by auto
          also have "... = {e \<in> X1. e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A} \<union> {e \<in> B. e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A}
              \<union> {e. (\<exists>ea. e = Event ea \<and> Event ea \<in> Y \<and> ea \<notin> A) \<and> e \<noteq> Tick \<and> e \<notin> Event ` A}"
            using nontock_sets by auto
          also have "... = {e. (e \<in> X1 \<or> e \<in> B \<or> (\<exists>ea. e = Event ea \<and> Event ea \<in> Y \<and> ea \<notin> A)) \<and> e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A}"
            by blast
          then show "{e. (e \<in> X2 \<or> e \<in> C \<or> (\<exists>ea. e = Event ea \<and> Event ea \<in> Y \<and> ea \<notin> A)) \<and> e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A} =
            {e. (e \<in> X1 \<or> e \<in> B \<or> (\<exists>ea. e = Event ea \<and> Event ea \<in> Y \<and> ea \<notin> A)) \<and> e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A}"
            using calculation by auto
        qed
      next
        fix p' X1 p'a X1a Aa
        assume case_assms2: "q = [[Tick]\<^sub>E]" "\<sigma>' \<in> p'a \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" "p = [X1a]\<^sub>R # [Tock]\<^sub>E # p'a"
          "[[X1a \<union> Event ` Aa]\<^sub>R] \<in> [[X1a]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" "Aa \<subseteq> A" "X = X1a \<union> Event ` Aa"
        have 1: "[[X1a]\<^sub>R, [Tock]\<^sub>E] \<in> P"
          using TT_P TT_empty TT_init_tock case_assms2(3) p_in_P by blast
        have 2: "B \<inter> {e. (e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> [[X1a]\<^sub>R, [e]\<^sub>E] \<in> P)} = {}"
          using nontock_P_assm1 nontock_sets by auto
        have 3: "{Event e |e. Event e \<in> Y \<and> e \<notin> A} \<inter> {Event e |e. e \<notin> A \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[Event e]\<^sub>E] \<in> x)} = {}"
          using assm1 bex_empty disjoint_iff_not_equal by blast
        have 4: "{Event e |e. Event e \<in> Y \<and> e \<notin> A} \<inter> ({Event ea |ea. ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> P} \<union> {Event ea |ea. ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> Q}) = {}"
          by (smt "3" disjoint_iff_not_equal set1 subsetCE)
        have 5: "(B \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A}) \<inter> {e. (e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> [[X1a]\<^sub>R, [e]\<^sub>E] \<in> P)} = {}"
          using 2 4 by blast
        have 6: "[X1a \<union> B \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A}]\<^sub>R # [Tock]\<^sub>E # p'a \<in> P"
          using case_assms2(3) p_in_P 5 TT2_P unfolding TT2_def apply (erule_tac x="[]" in allE, erule_tac x="[Tock]\<^sub>E # p'a" in allE)
          by (erule_tac x="X1a" in allE, erule_tac x="B \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A}" in allE, auto simp add: sup_assoc)
        have 7: "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<in> P \<lbrakk>A\<rbrakk>\<^sub>C Q"
          using assm2 case_assm p_in_P q_in_Q unfolding ParCompTT_def by auto
        have TT1_ParComp: "TT1 (P \<lbrakk>A\<rbrakk>\<^sub>C Q)"
          by (simp add: TT1_ParComp TT_P TT_Q)
        have 8: "[[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<lbrakk>A\<rbrakk>\<^sub>C Q"
          using 7 TT1_ParComp unfolding TT1_def apply (auto) by (erule_tac x="[[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto)
        have 9: "Tock \<in> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[e]\<^sub>E] \<in> x) \<or> e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> x)}"
          using 8 unfolding ParCompTT_def by auto
        have 10: "Tock \<notin> Y"
          using 9 assm1 by auto
        have 11: "[X1a \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A}]\<^sub>R # [Tock]\<^sub>E # p'a \<in> P"
          using TT2_P case_assms2(3) p_in_P 5 unfolding TT2_def apply auto
          apply (erule_tac x="[]" in allE, erule_tac x="[Tock]\<^sub>E # p'a" in allE)
          by (erule_tac x="X1a" in allE, erule_tac x="{Event e |e. Event e \<in> Y \<and> e \<notin> A}" in allE, auto)
        have 12: "Tick \<in> Y \<Longrightarrow> [[Tick]\<^sub>E] \<notin> P"
        proof auto
          assume Tick_in_Y: "Tick \<in> Y"
          assume Tick_in_P: "[[Tick]\<^sub>E] \<in> P"
          have "[[Tick]\<^sub>E] \<in> P \<lbrakk>A\<rbrakk>\<^sub>C Q"
            using Tick_in_P case_assms2(1) q_in_Q unfolding ParCompTT_def apply auto
            apply (rule_tac x="[[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" in exI, auto)
            by (rule_tac x="[[Tick]\<^sub>E]" in bexI, rule_tac x="[[Tick]\<^sub>E]" in bexI, auto)
          then have "Tick \<in> Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[e]\<^sub>E] \<in> x) \<or>
              e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> x)}"
            using Tick_in_Y Tick_in_P case_assms2(1) q_in_Q apply auto
            apply (rule_tac x="[[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" in exI, auto)
            by (rule_tac x="[[Tick]\<^sub>E]" in bexI, rule_tac x="[[Tick]\<^sub>E]" in bexI, auto)
          then show False
            using assm1 by auto
        qed
        then have 13: "Tick \<in> Y \<Longrightarrow> [X1a \<union> {Tick} \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A}]\<^sub>R # [Tock]\<^sub>E # p'a \<in> P"
        proof auto
          assume Tick_notin_P: "[[Tick]\<^sub>E] \<notin> P"
          then have "{Tick} \<inter> {e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> [[X1a \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A}]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
            by blast
          then show "[insert Tick (X1a \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A})]\<^sub>R # [Tock]\<^sub>E # p'a \<in> P"
            using TT2_P 11 unfolding TT2_def apply auto
            apply (erule_tac x="[]" in allE, erule_tac x="[Tock]\<^sub>E # p'a" in allE)
            by (erule_tac x="X1a \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A}" in allE, erule_tac x="{Tick}" in allE, auto)
        qed
        show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X1a \<union> Event ` Aa \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<in> x"
          using case_assms2 q_in_Q 10 11 13 apply (cases "Tick \<in> Y")
          apply (rule_tac x="([X1a \<union> {Tick} \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A}]\<^sub>R # [Tock]\<^sub>E # p'a) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([[Tick]\<^sub>E])" in exI)
          apply safe
          apply (rule_tac x="([X1a \<union> {Tick} \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A}]\<^sub>R # [Tock]\<^sub>E # p'a)" in bexI)
          apply (rule_tac x="[[Tick]\<^sub>E]" in bexI, simp_all)
          apply (rule_tac x="Aa \<union> {x\<in>A. Event x \<in> Y}" in exI, auto)
          apply (metis (mono_tags, lifting) "10" UnI2 imageI mem_Collect_eq ttevent.exhaust)
          apply (rule_tac x="([X1a \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A}]\<^sub>R # [Tock]\<^sub>E # p'a) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([[Tick]\<^sub>E])" in exI)
          apply safe
          apply (rule_tac x="([X1a \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A}]\<^sub>R # [Tock]\<^sub>E # p'a)" in bexI)
          apply (rule_tac x="[[Tick]\<^sub>E]" in bexI, auto)
          apply (rule_tac x="Aa \<union> {x\<in>A. Event x \<in> Y}" in exI, auto)
          apply (metis (mono_tags, lifting) "10" UnI2 imageI mem_Collect_eq ttevent.exhaust)
          done
      next
        fix q' X2 q'a X2a Aa
        assume case_assms2: "q = [X2a]\<^sub>R # [Tock]\<^sub>E # q'a" "\<sigma>' \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'a" "p = [[Tick]\<^sub>E]"
          "[[X2a \<union> Event ` Aa]\<^sub>R] \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[X2a]\<^sub>R]" "Aa \<subseteq> A" "X = X2a \<union> Event ` Aa"
        have 1: "[[X2a]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
          using TT_Q TT_empty TT_init_tock case_assms2 q_in_Q by blast
        have 2: "C \<inter> {e. (e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> Q) \<or> (e = Tock \<and> [[X2a]\<^sub>R, [e]\<^sub>E] \<in> Q)} = {}"
          using nontock_Q_assm1 nontock_sets by auto
        have 3: "{Event e |e. Event e \<in> Y \<and> e \<notin> A} \<inter> {Event e |e. e \<notin> A \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[Event e]\<^sub>E] \<in> x)} = {}"
          using assm1 bex_empty disjoint_iff_not_equal by blast
        have 4: "{Event e |e. Event e \<in> Y \<and> e \<notin> A} \<inter> ({Event ea |ea. ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> P} \<union> {Event ea |ea. ea \<notin> A \<and> [[Event ea]\<^sub>E] \<in> Q}) = {}"
          by (smt "3" disjoint_iff_not_equal set1 subsetCE)
        have 5: "(C \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A}) \<inter> {e. (e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> Q) \<or> (e = Tock \<and> [[X2a]\<^sub>R, [e]\<^sub>E] \<in> Q)} = {}"
          using 2 4 by blast
        have 6: "[X2a \<union> C \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A}]\<^sub>R # [Tock]\<^sub>E # q'a \<in> Q"
          using case_assms2(1) q_in_Q 5 TT2_Q unfolding TT2_def apply (erule_tac x="[]" in allE, erule_tac x="[Tock]\<^sub>E # q'a" in allE)
          by (erule_tac x="X2a" in allE, erule_tac x="C \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A}" in allE, auto simp add: sup_assoc)
        have 7: "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<in> P \<lbrakk>A\<rbrakk>\<^sub>C Q"
          using assm2 case_assm p_in_P q_in_Q unfolding ParCompTT_def by auto
        have TT1_ParComp: "TT1 (P \<lbrakk>A\<rbrakk>\<^sub>C Q)"
          by (simp add: TT1_ParComp TT_P TT_Q)
        have 8: "[[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<lbrakk>A\<rbrakk>\<^sub>C Q"
          using 7 TT1_ParComp unfolding TT1_def apply (auto) by (erule_tac x="[[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto)
        have 9: "Tock \<in> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[e]\<^sub>E] \<in> x) \<or> e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> x)}"
          using 8 unfolding ParCompTT_def by auto
        have 10: "Tock \<notin> Y"
          using 9 assm1 by auto
        have 11: "[X2a \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A}]\<^sub>R # [Tock]\<^sub>E # q'a \<in> Q"
          using TT2_Q case_assms2(1) q_in_Q 5 unfolding TT2_def apply auto
          apply (erule_tac x="[]" in allE, erule_tac x="[Tock]\<^sub>E # q'a" in allE)
          by (erule_tac x="X2a" in allE, erule_tac x="{Event e |e. Event e \<in> Y \<and> e \<notin> A}" in allE, auto)
        have 12: "Tick \<in> Y \<Longrightarrow> [[Tick]\<^sub>E] \<notin> Q"
        proof auto
          assume Tick_in_Y: "Tick \<in> Y"
          assume Tick_in_Q: "[[Tick]\<^sub>E] \<in> Q"
          have "[[Tick]\<^sub>E] \<in> P \<lbrakk>A\<rbrakk>\<^sub>C Q"
            using Tick_in_Q case_assms2(3) p_in_P unfolding ParCompTT_def apply auto
            apply (rule_tac x="[[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" in exI, auto)
            by (rule_tac x="[[Tick]\<^sub>E]" in bexI, rule_tac x="[[Tick]\<^sub>E]" in bexI, auto)
          then have "Tick \<in> Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[e]\<^sub>E] \<in> x) \<or>
              e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> x)}"
            using Tick_in_Y Tick_in_Q case_assms2(3) p_in_P apply auto
            apply (rule_tac x="[[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" in exI, auto)
            by (rule_tac x="[[Tick]\<^sub>E]" in bexI, rule_tac x="[[Tick]\<^sub>E]" in bexI, auto)
          then show False
            using assm1 by auto
        qed
        then have 13: "Tick \<in> Y \<Longrightarrow> [X2a \<union> {Tick} \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A}]\<^sub>R # [Tock]\<^sub>E # q'a \<in> Q"
        proof auto
          assume Tick_notin_P: "[[Tick]\<^sub>E] \<notin> Q"
          then have "{Tick} \<inter> {e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> [[X2a \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A}]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
            by blast
          then show "[insert Tick (X2a \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A})]\<^sub>R # [Tock]\<^sub>E # q'a \<in> Q"
            using TT2_Q 11 unfolding TT2_def apply auto
            apply (erule_tac x="[]" in allE, erule_tac x="[Tock]\<^sub>E # q'a" in allE)
            by (erule_tac x="X2a \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A}" in allE, erule_tac x="{Tick}" in allE, auto)
        qed
        show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X2a \<union> Event ` Aa \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<in> x"
          using case_assms2 p_in_P 10 11 13 apply (cases "Tick \<in> Y")
          apply (rule_tac x="([[Tick]\<^sub>E]) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([X2a \<union> {Tick} \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A}]\<^sub>R # [Tock]\<^sub>E # q'a)" in exI)
          apply safe
          apply (rule_tac x="[[Tick]\<^sub>E]" in bexI)
          apply (rule_tac x="([X2a \<union> {Tick} \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A}]\<^sub>R # [Tock]\<^sub>E # q'a)" in bexI, simp_all)
          apply (rule_tac x="Aa \<union> {x\<in>A. Event x \<in> Y}" in exI, auto)
          apply (metis (mono_tags, lifting) "10" UnI2 imageI mem_Collect_eq ttevent.exhaust)
          apply (rule_tac x="([[Tick]\<^sub>E]) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([X2a \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A}]\<^sub>R # [Tock]\<^sub>E # q'a)" in exI)
          apply safe
          apply (rule_tac x="[[Tick]\<^sub>E]" in bexI)
          apply (rule_tac x="([X2a \<union> {Event e |e. Event e \<in> Y \<and> e \<notin> A}]\<^sub>R # [Tock]\<^sub>E # q'a)" in bexI, simp_all)
          apply (rule_tac x="Aa \<union> {x\<in>A. Event x \<in> Y}" in exI, auto)
          apply (metis (mono_tags, lifting) "10" UnI2 imageI mem_Collect_eq ttevent.exhaust)
          done
      qed
    qed
  next
    fix X P Q Xa Y p q
    assume "[X]\<^sub>R # [Xa]\<^sub>R # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" " p \<in> P" "q \<in> Q" "TT P" "TT Q"
    then have "ttWF ([X]\<^sub>R # [Xa]\<^sub>R # \<sigma>)"
      using TT_wf merge_traces_wf by blast
    then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Xa \<union> Y]\<^sub>R # \<sigma> \<in> x"
      by auto
  next
    fix P Q X Y p q
    assume "[Tick]\<^sub>E # [X]\<^sub>R # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" " p \<in> P" "q \<in> Q" "TT P" "TT Q"
    then have "ttWF ([Tick]\<^sub>E # [X]\<^sub>R # \<sigma>)"
      using TT_wf merge_traces_wf by blast
    then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Tick]\<^sub>E # [X \<union> Y]\<^sub>R # \<sigma> \<in> x"
      by auto
  next
    fix P Q :: "'a ttobs list set"
    fix p q \<sigma>' :: "'a ttobs list"
    fix X Y :: "'a ttevent set"  
    fix e :: "'a"
    assume assm1: "[Event e]\<^sub>E # \<sigma>' @ [X]\<^sub>R # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    then have p_q_cases: "(\<exists> p' q'. e \<in> A \<and> p = [Event e]\<^sub>E # p' \<and> q = [Event e]\<^sub>E # q' \<and> \<sigma>' @ [X]\<^sub>R # \<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')
      \<or> (\<exists> p'. e \<notin> A \<and> p = [Event e]\<^sub>E # p' \<and> \<sigma>' @ [X]\<^sub>R # \<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q)
      \<or> (\<exists> q'. e \<notin> A \<and> q = [Event e]\<^sub>E # q' \<and> \<sigma>' @ [X]\<^sub>R # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
      by (cases "(p,q)" rule:ttWF2.cases, simp_all, blast)
    assume induction_hypothesis: "(\<And>P Q X Y p q. TT P \<Longrightarrow> TT Q \<Longrightarrow> TT2 P \<Longrightarrow> TT2 Q \<Longrightarrow>
      Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma>' @ [[e]\<^sub>E] \<in> x) \<or>
        e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma>' @ [[X]\<^sub>R, [e]\<^sub>E] \<in> x)} = {} \<Longrightarrow>
      \<sigma>' @ [X]\<^sub>R # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> p \<in> P \<Longrightarrow> q \<in> Q \<Longrightarrow> \<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma>' @ [X \<union> Y]\<^sub>R # \<sigma> \<in> x)"
    assume disjoint: "Y \<inter> {ea. ea \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Event e]\<^sub>E # \<sigma>' @ [[ea]\<^sub>E] \<in> x) \<or>
                 ea = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Event e]\<^sub>E # \<sigma>' @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> x)} = {}"
    assume p_P: "p \<in> P" and q_Q: "q \<in> Q"
    assume TT_P: "TT P" and TT_Q: "TT Q"
    assume TT2_P: "TT2 P" and TT2_Q: "TT2 Q"
    show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Event e]\<^sub>E # \<sigma>' @ [X \<union> Y]\<^sub>R # \<sigma> \<in> x"
      using p_q_cases
    proof auto
      fix p' q'
      assume case_assms: "e \<in> A" "p = [Event e]\<^sub>E # p'" "q = [Event e]\<^sub>E # q'" "\<sigma>' @ [X]\<^sub>R # \<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'"
      have 1: "TT {x. [Event e]\<^sub>E # x \<in> P}"
        using TT_P TT_init_event case_assms(2) p_P by force
      have 2: "TT {x. [Event e]\<^sub>E # x \<in> Q}"
        using TT_Q TT_init_event case_assms(3) q_Q by force
      have 3: "TT2 {x. [Event e]\<^sub>E # x \<in> P}"
        using TT2_P TT2_init_event by force
      have 4: "TT2 {x. [Event e]\<^sub>E # x \<in> Q}"
        using TT2_Q TT2_init_event by force
      have 5: "{ea. ea \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>{x. [Event e]\<^sub>E # x \<in> P}. \<exists>q\<in>{x. [Event e]\<^sub>E # x \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma>' @ [[ea]\<^sub>E] \<in> x) \<or>
          ea = Tock \<and> (\<exists>x. (\<exists>p\<in>{x. [Event e]\<^sub>E # x \<in> P}. \<exists>q\<in>{x. [Event e]\<^sub>E # x \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma>' @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> x)}
        \<subseteq> {ea. ea \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Event e]\<^sub>E # \<sigma>' @ [[ea]\<^sub>E] \<in> x) \<or>
          ea = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Event e]\<^sub>E # \<sigma>' @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> x)}"
        using case_assms apply auto
        apply (rule_tac x="([Event e]\<^sub>E # pa) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([Event e]\<^sub>E # qa)" in exI, fastforce)
        apply (rule_tac x="([Event e]\<^sub>E # pa) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([Event e]\<^sub>E # qa)" in exI, fastforce)
        apply (erule_tac x="([Event e]\<^sub>E # pa) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([Event e]\<^sub>E # qa)" in allE, fastforce)
        apply (erule_tac x="([Event e]\<^sub>E # pa) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([Event e]\<^sub>E # qa)" in allE, fastforce)
        done
      then have 6: "Y \<inter> {ea. ea \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>{x. [Event e]\<^sub>E # x \<in> P}. \<exists>q\<in>{x. [Event e]\<^sub>E # x \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma>' @ [[ea]\<^sub>E] \<in> x) \<or>
          ea = Tock \<and> (\<exists>x. (\<exists>p\<in>{x. [Event e]\<^sub>E # x \<in> P}. \<exists>q\<in>{x. [Event e]\<^sub>E # x \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma>' @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> x)} = {}"
        by (smt disjoint disjoint_iff_not_equal subsetCE)
      have "\<exists>x. (\<exists>p\<in>{x. [Event e]\<^sub>E # x \<in> P}. \<exists>q\<in>{x. [Event e]\<^sub>E # x \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma>' @ [X \<union> Y]\<^sub>R # \<sigma> \<in> x"
        using 1 2 3 4 6 case_assms p_P q_Q induction_hypothesis[where P="{x. [Event e]\<^sub>E # x \<in> P}", where Q="{x. [Event e]\<^sub>E # x \<in> Q}"] by force
      then obtain pa qa where "pa\<in>{x. [Event e]\<^sub>E # x \<in> P}" "qa\<in>{x. [Event e]\<^sub>E # x \<in> Q}" "\<sigma>' @ [X \<union> Y]\<^sub>R # \<sigma> \<in> pa \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C qa"
        by auto
      then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Event e]\<^sub>E # \<sigma>' @ [X \<union> Y]\<^sub>R # \<sigma> \<in> x"
        using case_assms by (rule_tac x="([Event e]\<^sub>E # pa) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([Event e]\<^sub>E # qa)" in exI, fastforce)
    next
      fix p'
      assume case_assms: "e \<notin> A" "p = [Event e]\<^sub>E # p'" "\<sigma>' @ [X]\<^sub>R # \<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
      have 1: "TT {x. [Event e]\<^sub>E # x \<in> P}"
        using TT_P TT_init_event case_assms(2) p_P by force
      have 2: "TT2 {x. [Event e]\<^sub>E # x \<in> P}"
        using TT2_P TT2_init_event by force
      have 3: "{ea. ea \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>{x. [Event e]\<^sub>E # x \<in> P}. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma>' @ [[ea]\<^sub>E] \<in> x) \<or>
          ea = Tock \<and> (\<exists>x. (\<exists>p\<in>{x. [Event e]\<^sub>E # x \<in> P}. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma>' @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> x)}
        \<subseteq> {ea. ea \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Event e]\<^sub>E # \<sigma>' @ [[ea]\<^sub>E] \<in> x) \<or>
          ea = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Event e]\<^sub>E # \<sigma>' @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> x)}"
        using case_assms apply auto
        apply (rule_tac x="([Event e]\<^sub>E # pa) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C (qa)" in exI, auto, case_tac qa rule:ttWF.cases, auto)
        apply (rule_tac x="([Event e]\<^sub>E # pa) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C (qa)" in exI, auto, case_tac qa rule:ttWF.cases, auto)
        apply (erule_tac x="([Event e]\<^sub>E # pa) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C (qa)" in allE, auto, case_tac qa rule:ttWF.cases, auto)
        apply (erule_tac x="([Event e]\<^sub>E # pa) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C (qa)" in allE, auto, case_tac qa rule:ttWF.cases, auto)
        done
      then have 4: "Y \<inter> {ea. ea \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>{x. [Event e]\<^sub>E # x \<in> P}. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma>' @ [[ea]\<^sub>E] \<in> x) \<or>
          ea = Tock \<and> (\<exists>x. (\<exists>p\<in>{x. [Event e]\<^sub>E # x \<in> P}. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma>' @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> x)} = {}"
        by (smt disjoint disjoint_iff_not_equal subsetCE)
      have "\<exists>x. (\<exists>p\<in>{x. [Event e]\<^sub>E # x \<in> P}. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma>' @ [X \<union> Y]\<^sub>R # \<sigma> \<in> x"
        using 1 2 4 case_assms p_P q_Q TT2_Q TT_Q induction_hypothesis[where P="{x. [Event e]\<^sub>E # x \<in> P}"] by force
      then obtain pa qa where "pa\<in>{x. [Event e]\<^sub>E # x \<in> P}" "qa\<in>Q" "\<sigma>' @ [X \<union> Y]\<^sub>R # \<sigma> \<in> pa \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C qa"
        by auto
      then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Event e]\<^sub>E # \<sigma>' @ [X \<union> Y]\<^sub>R # \<sigma> \<in> x"
        using case_assms by (rule_tac x="([Event e]\<^sub>E # pa) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C (qa)" in exI, auto, cases qa rule:ttWF.cases, auto)
    next
      fix q'
      assume case_assms: "e \<notin> A" "q = [Event e]\<^sub>E # q'" "\<sigma>' @ [X]\<^sub>R # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'"
      have 1: "TT {x. [Event e]\<^sub>E # x \<in> Q}"
        using TT_Q TT_init_event case_assms(2) q_Q by force
      have 2: "TT2 {x. [Event e]\<^sub>E # x \<in> Q}"
        using TT2_Q TT2_init_event by force
      have 3: "{ea. ea \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>{x. [Event e]\<^sub>E # x \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma>' @ [[ea]\<^sub>E] \<in> x) \<or>
          ea = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>{x. [Event e]\<^sub>E # x \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma>' @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> x)}
        \<subseteq> {ea. ea \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Event e]\<^sub>E # \<sigma>' @ [[ea]\<^sub>E] \<in> x) \<or>
          ea = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Event e]\<^sub>E # \<sigma>' @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> x)}"
        using case_assms apply auto
        apply (rule_tac x="(pa) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([Event e]\<^sub>E # qa)" in exI, auto, case_tac pa rule:ttWF.cases, auto)
        apply (rule_tac x="(pa) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([Event e]\<^sub>E # qa)" in exI, auto, case_tac pa rule:ttWF.cases, auto)
        apply (erule_tac x="(pa) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([Event e]\<^sub>E # qa)" in allE, auto, case_tac pa rule:ttWF.cases, auto)
        apply (erule_tac x="(pa) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([Event e]\<^sub>E # qa)" in allE, auto, case_tac pa rule:ttWF.cases, auto)
        done
      then have 4: "Y \<inter> {ea. ea \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>{x. [Event e]\<^sub>E # x \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma>' @ [[ea]\<^sub>E] \<in> x) \<or>
          ea = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>{x. [Event e]\<^sub>E # x \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma>' @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> x)} = {}"
        by (smt disjoint disjoint_iff_not_equal subsetCE)
      have "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>{x. [Event e]\<^sub>E # x \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma>' @ [X \<union> Y]\<^sub>R # \<sigma> \<in> x"
        using 1 2 4 case_assms p_P q_Q TT2_P TT_P induction_hypothesis[where Q="{x. [Event e]\<^sub>E # x \<in> Q}"] by force
      then obtain pa qa where "pa\<in>P" "qa\<in>{x. [Event e]\<^sub>E # x \<in> Q}" "\<sigma>' @ [X \<union> Y]\<^sub>R # \<sigma> \<in> pa \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C qa"
        by auto
      then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Event e]\<^sub>E # \<sigma>' @ [X \<union> Y]\<^sub>R # \<sigma> \<in> x"
        using case_assms by (rule_tac x="(pa) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([Event e]\<^sub>E # qa)" in exI, auto, cases pa rule:ttWF.cases, auto)
    qed
  next
    fix P Q :: "'a ttobs list set"
    fix p q \<sigma>' :: "'a ttobs list"
    fix X Y Xa :: "'a ttevent set"  
    assume assm1: "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [Xa]\<^sub>R # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    then have p_q_cases: "(\<exists> p' q' X1 X2. p = [X1]\<^sub>R # [Tock]\<^sub>E # p' \<and> q = [X2]\<^sub>R # [Tock]\<^sub>E # q' \<and> [[X]\<^sub>R] \<in> ([[X1]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[X2]\<^sub>R]) \<and> \<sigma>' @ [Xa]\<^sub>R # \<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q') \<or>
      (\<exists> p' X1. p = [X1]\<^sub>R # [Tock]\<^sub>E # p' \<and> q = [[Tick]\<^sub>E] \<and> [[X]\<^sub>R] \<in> ([[X1]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]) \<and> \<sigma>' @ [Xa]\<^sub>R # \<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]) \<or>
      (\<exists> q' X2. p = [[Tick]\<^sub>E] \<and> q = [X2]\<^sub>R # [Tock]\<^sub>E # q' \<and> [[X]\<^sub>R] \<in> ([[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[X2]\<^sub>R]) \<and> \<sigma>' @ [Xa]\<^sub>R # \<sigma> \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
      by (cases "(p,q)" rule:ttWF2.cases, simp_all)
    assume induction_hypothesis: "\<And>P Q X Y p q. TT P \<Longrightarrow> TT Q \<Longrightarrow> TT2 P \<Longrightarrow> TT2 Q \<Longrightarrow>
      Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma>' @ [[e]\<^sub>E] \<in> x) \<or>
                    e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma>' @ [[X]\<^sub>R, [e]\<^sub>E] \<in> x)} = {} \<Longrightarrow>
      \<sigma>' @ [X]\<^sub>R # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> p \<in> P \<Longrightarrow> q \<in> Q \<Longrightarrow> \<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma>' @ [X \<union> Y]\<^sub>R # \<sigma> \<in> x"
    assume disjoint: "Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [[e]\<^sub>E] \<in> x) \<or>
                e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)} = {}"
    assume p_P: "p \<in> P" and q_Q: "q \<in> Q"
    assume TT_P: "TT P" and TT_Q: "TT Q"
    assume TT2_P: "TT2 P" and TT2_Q: "TT2 Q"
    show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [Xa \<union> Y]\<^sub>R # \<sigma> \<in> x"
      using p_q_cases
    proof safe
      fix p' q' X1 X2
      assume case_assms: "p = [X1]\<^sub>R # [Tock]\<^sub>E # p'" "q = [X2]\<^sub>R # [Tock]\<^sub>E # q'" "[[X]\<^sub>R] \<in> [[X1]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[X2]\<^sub>R]" "\<sigma>' @ [Xa]\<^sub>R # \<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'"
      have 1: "TT {x. [X1]\<^sub>R # [Tock]\<^sub>E # x \<in> P}"
        using TT_P TT_init_tock case_assms(1) p_P by blast
      have 2: "TT {x. [X2]\<^sub>R # [Tock]\<^sub>E # x \<in> Q}"
        using TT_Q TT_init_tock case_assms(2) q_Q by blast
      have 3: "TT2 {x. [X1]\<^sub>R # [Tock]\<^sub>E # x \<in> P}"
        using TT2_P TT2_init_tock by blast
      have 4: "TT2 {x. [X2]\<^sub>R # [Tock]\<^sub>E # x \<in> Q}"
        using TT2_Q TT2_init_tock by blast
      have 5: "{e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>{x. [X1]\<^sub>R # [Tock]\<^sub>E # x \<in> P}. \<exists>q\<in>{x. [X2]\<^sub>R # [Tock]\<^sub>E # x \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma>' @ [[e]\<^sub>E] \<in> x) \<or>
          e = Tock \<and> (\<exists>x. (\<exists>p\<in>{x. [X1]\<^sub>R # [Tock]\<^sub>E # x \<in> P}. \<exists>q\<in>{x. [X2]\<^sub>R # [Tock]\<^sub>E # x \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma>' @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)}
        \<subseteq> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [[e]\<^sub>E] \<in> x) \<or>
          e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)}"
        apply (auto, insert case_assms p_P q_Q)
        apply (rule_tac x="([X1]\<^sub>R # [Tock]\<^sub>E # pa) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([X2]\<^sub>R # [Tock]\<^sub>E # qa)" in exI, simp_all)
        apply (rule_tac x="([X1]\<^sub>R # [Tock]\<^sub>E # pa)" in bexI, rule_tac x="([X2]\<^sub>R # [Tock]\<^sub>E # qa)" in bexI, simp_all)
        apply (rule_tac x="([X1]\<^sub>R # [Tock]\<^sub>E # pa) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([X2]\<^sub>R # [Tock]\<^sub>E # qa)" in exI, simp_all)
        apply (rule_tac x="([X1]\<^sub>R # [Tock]\<^sub>E # pa)" in bexI, rule_tac x="([X2]\<^sub>R # [Tock]\<^sub>E # qa)" in bexI, simp_all)
        apply (erule_tac x="([X1]\<^sub>R # [Tock]\<^sub>E # pa) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([X2]\<^sub>R # [Tock]\<^sub>E # qa)" in allE, simp_all)
        apply (erule_tac x="([X1]\<^sub>R # [Tock]\<^sub>E # pa)" in ballE, erule_tac x="([X2]\<^sub>R # [Tock]\<^sub>E # qa)" in ballE, simp_all)
        apply (erule_tac x="([X1]\<^sub>R # [Tock]\<^sub>E # pa) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([X2]\<^sub>R # [Tock]\<^sub>E # qa)" in allE, simp_all)
        apply (erule_tac x="([X1]\<^sub>R # [Tock]\<^sub>E # pa)" in ballE, erule_tac x="([X2]\<^sub>R # [Tock]\<^sub>E # qa)" in ballE, simp_all)
        done
      then have 6: "Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>{x. [X1]\<^sub>R # [Tock]\<^sub>E # x \<in> P}. \<exists>q\<in>{x. [X2]\<^sub>R # [Tock]\<^sub>E # x \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma>' @ [[e]\<^sub>E] \<in> x) \<or>
          e = Tock \<and> (\<exists>x. (\<exists>p\<in>{x. [X1]\<^sub>R # [Tock]\<^sub>E # x \<in> P}. \<exists>q\<in>{x. [X2]\<^sub>R # [Tock]\<^sub>E # x \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma>' @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)} = {}"
        by (smt disjoint disjoint_iff_not_equal subsetCE)
      have "\<exists>x. (\<exists>p\<in>{x. [X1]\<^sub>R # [Tock]\<^sub>E # x \<in> P}. \<exists>q\<in>{x. [X2]\<^sub>R # [Tock]\<^sub>E # x \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma>' @ [Xa \<union> Y]\<^sub>R # \<sigma> \<in> x"
        using 1 2 3 4 6 case_assms p_P q_Q induction_hypothesis[where P="{x. [X1]\<^sub>R # [Tock]\<^sub>E # x \<in> P}", where Q="{x. [X2]\<^sub>R # [Tock]\<^sub>E # x \<in> Q}"] by fastforce
      then obtain pa qa where "pa \<in> {x. [X1]\<^sub>R # [Tock]\<^sub>E # x \<in> P}" "qa \<in> {x. [X2]\<^sub>R # [Tock]\<^sub>E # x \<in> Q}" "\<sigma>' @ [Xa \<union> Y]\<^sub>R # \<sigma> \<in> pa \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C qa"
        by auto
      then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [Xa \<union> Y]\<^sub>R # \<sigma> \<in> x"
        using case_assms apply (rule_tac x="([X1]\<^sub>R # [Tock]\<^sub>E # pa) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([X2]\<^sub>R # [Tock]\<^sub>E # qa)" in exI, simp_all)
        by (rule_tac x="([X1]\<^sub>R # [Tock]\<^sub>E # pa)" in bexI, rule_tac x="([X2]\<^sub>R # [Tock]\<^sub>E # qa)" in bexI, simp_all)
    next
      fix p' X1
      assume case_assms: "p = [X1]\<^sub>R # [Tock]\<^sub>E # p'" "q = [[Tick]\<^sub>E]" "[[X]\<^sub>R] \<in> [[X1]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" "\<sigma>' @ [Xa]\<^sub>R # \<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
      have 1: "TT {x. [X1]\<^sub>R # [Tock]\<^sub>E # x \<in> P}"
        using TT_P TT_init_tock case_assms(1) p_P by blast
      have 2: "TT {[], [[Tick]\<^sub>E]}"
        by (metis TT_Skip SkipTT_def)
      have 3: "TT2 {x. [X1]\<^sub>R # [Tock]\<^sub>E # x \<in> P}"
        using TT2_P TT2_init_tock by blast
      have 4: "TT2 {[], [[Tick]\<^sub>E]}"
        by (metis TT2_Skip SkipTT_def)
      have 5: "{e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>{x. [X1]\<^sub>R # [Tock]\<^sub>E # x \<in> P}. \<exists>q\<in>{[], [[Tick]\<^sub>E]}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma>' @ [[e]\<^sub>E] \<in> x) \<or>
          e = Tock \<and> (\<exists>x. (\<exists>p\<in>{x. [X1]\<^sub>R # [Tock]\<^sub>E # x \<in> P}. \<exists>q\<in>{[], [[Tick]\<^sub>E]}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma>' @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)}
        \<subseteq> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [[e]\<^sub>E] \<in> x) \<or>
          e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)}"
      proof auto
        fix x p
        assume case_assms2: "\<sigma>' @ [[x]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C []" "[X1]\<^sub>R # [Tock]\<^sub>E # p \<in> P" "x \<noteq> Tock"
        obtain t where t_assms: "t \<lesssim>\<^sub>C p \<and> \<sigma>' @ [[x]\<^sub>E] \<in> t \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
          using case_assms2(1) merge_traces_empty_merge_traces_tick by blast
        have "[X1]\<^sub>R # [Tock]\<^sub>E # t \<in> P"
          by (metis (mono_tags, lifting) "1" TT1_def TT_def case_assms2(2) mem_Collect_eq t_assms)
        then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [[x]\<^sub>E] \<in> xa"
          using case_assms case_assms2 t_assms q_Q
          apply (rule_tac x="([X1]\<^sub>R # [Tock]\<^sub>E # t) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([[Tick]\<^sub>E])" in exI, simp)
          by (rule_tac x="([X1]\<^sub>R # [Tock]\<^sub>E # t)" in bexI, rule_tac x="[[Tick]\<^sub>E]" in bexI, simp_all)
      next
        fix x p
        assume case_assms2: "\<sigma>' @ [[x]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C []" "[X1]\<^sub>R # [Tock]\<^sub>E # p \<in> P" "x \<noteq> Tock"
        obtain t where t_assms: "t \<lesssim>\<^sub>C p \<and> \<sigma>' @ [[x]\<^sub>E] \<in> t \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
          using case_assms2(1) merge_traces_empty_merge_traces_tick by blast
        have "[X1]\<^sub>R # [Tock]\<^sub>E # t \<in> P"
          by (metis (mono_tags, lifting) "1" TT1_def TT_def case_assms2(2) mem_Collect_eq t_assms)
        then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [[x]\<^sub>E] \<in> xa"
          using case_assms case_assms2 t_assms q_Q
          apply (rule_tac x="([X1]\<^sub>R # [Tock]\<^sub>E # t) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([[Tick]\<^sub>E])" in exI, simp)
          by (rule_tac x="([X1]\<^sub>R # [Tock]\<^sub>E # t)" in bexI, rule_tac x="[[Tick]\<^sub>E]" in bexI, simp_all)
      next  
        fix x p
        assume case_assms2: "\<sigma>' @ [[x]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" "[X1]\<^sub>R # [Tock]\<^sub>E # p \<in> P" "x \<noteq> Tock"
        show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [[x]\<^sub>E] \<in> xa"
          using case_assms case_assms2 q_Q
          apply (rule_tac x="([X1]\<^sub>R # [Tock]\<^sub>E # p) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([[Tick]\<^sub>E])" in exI, simp)
          by (rule_tac x="([X1]\<^sub>R # [Tock]\<^sub>E # p)" in bexI, rule_tac x="[[Tick]\<^sub>E]" in bexI, simp_all)
      next  
        fix x p
        assume case_assms2: "\<sigma>' @ [[x]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" "[X1]\<^sub>R # [Tock]\<^sub>E # p \<in> P" "x \<noteq> Tock"
        show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [[x]\<^sub>E] \<in> xa"
          using case_assms case_assms2 q_Q
          apply (rule_tac x="([X1]\<^sub>R # [Tock]\<^sub>E # p) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([[Tick]\<^sub>E])" in exI, simp)
          by (rule_tac x="([X1]\<^sub>R # [Tock]\<^sub>E # p)" in bexI, rule_tac x="[[Tick]\<^sub>E]" in bexI, simp_all)
      next  
        fix p
        assume case_assms2: "\<sigma>' @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C []" "[X1]\<^sub>R # [Tock]\<^sub>E # p \<in> P"
        obtain t where t_assms: "t \<lesssim>\<^sub>C p \<and> \<sigma>' @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<in> t \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
          using case_assms2(1) merge_traces_empty_merge_traces_tick by blast
        have "[X1]\<^sub>R # [Tock]\<^sub>E # t \<in> P"
          by (metis (mono_tags, lifting) "1" TT1_def TT_def case_assms2(2) mem_Collect_eq t_assms)
        then show "\<forall>x. (\<forall>p\<in>P. \<forall>q\<in>Q. x \<noteq> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<or> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<notin> x \<Longrightarrow> False"
          using case_assms case_assms2 t_assms q_Q
          apply (erule_tac x="([X1]\<^sub>R # [Tock]\<^sub>E # t) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([[Tick]\<^sub>E])" in allE, simp)
          by (erule_tac x="([X1]\<^sub>R # [Tock]\<^sub>E # t)" in ballE, erule_tac x="[[Tick]\<^sub>E]" in ballE, simp_all)
      next  
        fix p
        assume case_assms2: "\<sigma>' @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C []" "[X1]\<^sub>R # [Tock]\<^sub>E # p \<in> P"
        obtain t where t_assms: "t \<lesssim>\<^sub>C p \<and> \<sigma>' @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<in> t \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
          using case_assms2(1) merge_traces_empty_merge_traces_tick by blast
        have "[X1]\<^sub>R # [Tock]\<^sub>E # t \<in> P"
          by (metis (mono_tags, lifting) "1" TT1_def TT_def case_assms2(2) mem_Collect_eq t_assms)
        then show "\<forall>x. (\<forall>p\<in>P. \<forall>q\<in>Q. x \<noteq> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<or> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<notin> x \<Longrightarrow>
          \<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [[Tock]\<^sub>E] \<in> x"
          using case_assms case_assms2 t_assms q_Q
          apply (erule_tac x="([X1]\<^sub>R # [Tock]\<^sub>E # t) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([[Tick]\<^sub>E])" in allE, simp)
          by (erule_tac x="([X1]\<^sub>R # [Tock]\<^sub>E # t)" in ballE, erule_tac x="[[Tick]\<^sub>E]" in ballE, simp_all)
      next  
        fix p
        assume case_assms2: "\<sigma>' @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" "[X1]\<^sub>R # [Tock]\<^sub>E # p \<in> P"
        then show "\<forall>x. (\<forall>p\<in>P. \<forall>q\<in>Q. x \<noteq> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<or> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<notin> x \<Longrightarrow>
          \<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [[Tock]\<^sub>E] \<in> x"
          using case_assms case_assms2 q_Q
          apply (erule_tac x="([X1]\<^sub>R # [Tock]\<^sub>E # p) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([[Tick]\<^sub>E])" in allE, simp)
          by (erule_tac x="([X1]\<^sub>R # [Tock]\<^sub>E # p)" in ballE, erule_tac x="[[Tick]\<^sub>E]" in ballE, simp_all)
      next  
        fix p
        assume case_assms2: "\<sigma>' @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" "[X1]\<^sub>R # [Tock]\<^sub>E # p \<in> P"
        then show "\<forall>x. (\<forall>p\<in>P. \<forall>q\<in>Q. x \<noteq> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<or> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<notin> x \<Longrightarrow> False"
          using case_assms case_assms2 q_Q
          apply (erule_tac x="([X1]\<^sub>R # [Tock]\<^sub>E # p) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([[Tick]\<^sub>E])" in allE, simp)
          by (erule_tac x="([X1]\<^sub>R # [Tock]\<^sub>E # p)" in ballE, erule_tac x="[[Tick]\<^sub>E]" in ballE, simp_all)
      qed
      then have 6: "Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>{x. [X1]\<^sub>R # [Tock]\<^sub>E # x \<in> P}. \<exists>q\<in>{[], [[Tick]\<^sub>E]}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma>' @ [[e]\<^sub>E] \<in> x) \<or>
        e = Tock \<and> (\<exists>x. (\<exists>p\<in>{x. [X1]\<^sub>R # [Tock]\<^sub>E # x \<in> P}. \<exists>q\<in>{[], [[Tick]\<^sub>E]}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma>' @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)} = {}"
        by (smt disjoint disjoint_iff_not_equal subsetCE)
      then have "\<exists>x. (\<exists>p\<in>{x. [X1]\<^sub>R # [Tock]\<^sub>E # x \<in> P}. \<exists>q\<in>{[], [[Tick]\<^sub>E]}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma>' @ [Xa \<union> Y]\<^sub>R # \<sigma> \<in> x"
        using 1 2 3 4 6 p_P q_Q case_assms induction_hypothesis[where P="{x. [X1]\<^sub>R # [Tock]\<^sub>E # x \<in> P}", where Q="{[], [[Tick]\<^sub>E]}"] by fastforce
      then obtain pa where "pa \<in> {x. [X1]\<^sub>R # [Tock]\<^sub>E # x \<in> P}" "\<sigma>' @ [Xa \<union> Y]\<^sub>R # \<sigma> \<in> pa \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
        by (auto, metis (no_types, lifting) "1" TT1_def TT_def mem_Collect_eq merge_traces_empty_merge_traces_tick)
      then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [Xa \<union> Y]\<^sub>R # \<sigma> \<in> x"
        using case_assms q_Q apply (rule_tac x="([X1]\<^sub>R # [Tock]\<^sub>E # pa) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([[Tick]\<^sub>E])" in exI, simp_all)
        by (rule_tac x="([X1]\<^sub>R # [Tock]\<^sub>E # pa)" in bexI, rule_tac x="[[Tick]\<^sub>E]" in bexI, simp_all)
    next
      fix q' X2
      assume case_assms: "p = [[Tick]\<^sub>E]" "q = [X2]\<^sub>R # [Tock]\<^sub>E # q'" "[[X]\<^sub>R] \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[X2]\<^sub>R]" "\<sigma>' @ [Xa]\<^sub>R # \<sigma> \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'"
      have 1: "TT {x. [X2]\<^sub>R # [Tock]\<^sub>E # x \<in> Q}"
        using TT_Q TT_init_tock case_assms(2) q_Q by blast
      have 2: "TT {[], [[Tick]\<^sub>E]}"
        by (metis TT_Skip SkipTT_def)
      have 3: "TT2 {x. [X2]\<^sub>R # [Tock]\<^sub>E # x \<in> Q}"
        using TT2_Q TT2_init_tock by blast
      have 4: "TT2 {[], [[Tick]\<^sub>E]}"
        by (metis TT2_Skip SkipTT_def)
      have 5: "{e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>{[], [[Tick]\<^sub>E]}. \<exists>q\<in>{x. [X2]\<^sub>R # [Tock]\<^sub>E # x \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma>' @ [[e]\<^sub>E] \<in> x) \<or>
          e = Tock \<and> (\<exists>x. (\<exists>p\<in>{[], [[Tick]\<^sub>E]}. \<exists>q\<in>{x. [X2]\<^sub>R # [Tock]\<^sub>E # x \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma>' @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)}
        \<subseteq> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [[e]\<^sub>E] \<in> x) \<or>
          e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)}"
      proof auto
        fix x q
        assume case_assms2: "\<sigma>' @ [[x]\<^sub>E] \<in> [] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "[X2]\<^sub>R # [Tock]\<^sub>E # q \<in> Q" "x \<noteq> Tock"
        obtain t where t_assms: "t \<lesssim>\<^sub>C q \<and> \<sigma>' @ [[x]\<^sub>E] \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C t"
          using case_assms2(1) merge_traces_comm merge_traces_empty_merge_traces_tick by blast
        have "[X2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q"
          by (metis (mono_tags, lifting) "1" TT1_def TT_def case_assms2(2) mem_Collect_eq t_assms)
        then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [[x]\<^sub>E] \<in> xa"
          using case_assms case_assms2 t_assms p_P p_q_cases
          apply (rule_tac x="([[Tick]\<^sub>E]) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([X2]\<^sub>R # [Tock]\<^sub>E # t)" in exI, safe)
          by (rule_tac x="[[Tick]\<^sub>E]" in bexI, rule_tac x="([X2]\<^sub>R # [Tock]\<^sub>E # t)" in bexI, simp_all)
      next
        fix x q
        assume case_assms2: "\<sigma>' @ [[x]\<^sub>E] \<in> [] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "[X2]\<^sub>R # [Tock]\<^sub>E # q \<in> Q" "x \<noteq> Tock"
        obtain t where t_assms: "t \<lesssim>\<^sub>C q \<and> \<sigma>' @ [[x]\<^sub>E] \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C t"
          using case_assms2(1) merge_traces_comm merge_traces_empty_merge_traces_tick by blast
        have "[X2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q"
          by (metis (mono_tags, lifting) "1" TT1_def TT_def case_assms2(2) mem_Collect_eq t_assms)
        then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [[x]\<^sub>E] \<in> xa"
          using case_assms case_assms2 t_assms p_P p_q_cases
          apply (rule_tac x="([[Tick]\<^sub>E]) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([X2]\<^sub>R # [Tock]\<^sub>E # t)" in exI, simp)
          by (rule_tac x="[[Tick]\<^sub>E]" in bexI, rule_tac x="([X2]\<^sub>R # [Tock]\<^sub>E # t)" in bexI, simp_all)
      next
        fix x q
        assume case_assms2: "\<sigma>' @ [[x]\<^sub>E] \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "[X2]\<^sub>R # [Tock]\<^sub>E # q \<in> Q" "x \<noteq> Tock"
        show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [[x]\<^sub>E] \<in> xa"
          using case_assms case_assms2 p_P p_q_cases
          apply (rule_tac x="([[Tick]\<^sub>E]) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([X2]\<^sub>R # [Tock]\<^sub>E # q)" in exI, simp)
          by (rule_tac x="[[Tick]\<^sub>E]" in bexI, rule_tac x="([X2]\<^sub>R # [Tock]\<^sub>E # q)" in bexI, simp_all)
      next
        fix x q
        assume case_assms2: "\<sigma>' @ [[x]\<^sub>E] \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "[X2]\<^sub>R # [Tock]\<^sub>E # q \<in> Q" "x \<noteq> Tock"
        show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [[x]\<^sub>E] \<in> xa"
          using case_assms case_assms2 p_P p_q_cases
          apply (rule_tac x="([[Tick]\<^sub>E]) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([X2]\<^sub>R # [Tock]\<^sub>E # q)" in exI, simp)
          by (rule_tac x="[[Tick]\<^sub>E]" in bexI, rule_tac x="([X2]\<^sub>R # [Tock]\<^sub>E # q)" in bexI, simp_all)
      next
        fix q
        assume case_assms2: "\<sigma>' @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<in> [] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "[X2]\<^sub>R # [Tock]\<^sub>E # q \<in> Q"
        obtain t where t_assms: "t \<lesssim>\<^sub>C q \<and> \<sigma>' @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C t"
          using case_assms2(1) merge_traces_comm merge_traces_empty_merge_traces_tick by blast
        have "[X2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q"
          by (metis (mono_tags, lifting) "1" TT1_def TT_def case_assms2(2) mem_Collect_eq t_assms)
        then show "\<forall>x. (\<forall>p\<in>P. \<forall>q\<in>Q. x \<noteq> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<or> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<notin> x \<Longrightarrow> False"
          using case_assms case_assms2 t_assms p_P p_q_cases
          apply (erule_tac x="([[Tick]\<^sub>E]) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([X2]\<^sub>R # [Tock]\<^sub>E # t)" in allE, simp)
          by (erule_tac x="[[Tick]\<^sub>E]" in ballE, erule_tac x="([X2]\<^sub>R # [Tock]\<^sub>E # t)" in ballE, simp_all)
      next
        fix q
        assume case_assms2: "\<sigma>' @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<in> [] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "[X2]\<^sub>R # [Tock]\<^sub>E # q \<in> Q"
        obtain t where t_assms: "t \<lesssim>\<^sub>C q \<and> \<sigma>' @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C t"
          using case_assms2(1) merge_traces_comm merge_traces_empty_merge_traces_tick by blast
        have "[X2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q"
          by (metis (mono_tags, lifting) "1" TT1_def TT_def case_assms2(2) mem_Collect_eq t_assms)
        then show "\<forall>x. (\<forall>p\<in>P. \<forall>q\<in>Q. x \<noteq> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<or> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<notin> x \<Longrightarrow>
          \<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [[Tock]\<^sub>E] \<in> x"
          using case_assms case_assms2 t_assms p_P p_q_cases
          apply (erule_tac x="([[Tick]\<^sub>E]) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([X2]\<^sub>R # [Tock]\<^sub>E # t)" in allE, simp)
          by (erule_tac x="[[Tick]\<^sub>E]" in ballE, erule_tac x="([X2]\<^sub>R # [Tock]\<^sub>E # t)" in ballE, simp_all)
      next  
        fix q
        assume case_assms2: "\<sigma>' @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "[X2]\<^sub>R # [Tock]\<^sub>E # q \<in> Q"
        then show "\<forall>x. (\<forall>p\<in>P. \<forall>q\<in>Q. x \<noteq> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<or> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<notin> x \<Longrightarrow>
          \<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [[Tock]\<^sub>E] \<in> x"
          using case_assms case_assms2 p_P p_q_cases
          apply (erule_tac x="([[Tick]\<^sub>E]) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([X2]\<^sub>R # [Tock]\<^sub>E # q)" in allE, simp)
          by (erule_tac x="[[Tick]\<^sub>E]" in ballE, erule_tac x="([X2]\<^sub>R # [Tock]\<^sub>E # q)" in ballE, simp_all)
      next  
        fix q
        assume case_assms2: "\<sigma>' @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "[X2]\<^sub>R # [Tock]\<^sub>E # q \<in> Q"
        then show "\<forall>x. (\<forall>p\<in>P. \<forall>q\<in>Q. x \<noteq> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<or> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [[Xa]\<^sub>R, [Tock]\<^sub>E] \<notin> x \<Longrightarrow> False"
          using case_assms case_assms2 p_P p_q_cases
          apply (erule_tac x="([[Tick]\<^sub>E]) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([X2]\<^sub>R # [Tock]\<^sub>E # q)" in allE, simp)
          by (erule_tac x="[[Tick]\<^sub>E]" in ballE, erule_tac x="([X2]\<^sub>R # [Tock]\<^sub>E # q)" in ballE, simp_all)
      qed
      then have 6: "Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>{[], [[Tick]\<^sub>E]}. \<exists>q\<in>{x. [X2]\<^sub>R # [Tock]\<^sub>E # x \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma>' @ [[e]\<^sub>E] \<in> x) \<or>
          e = Tock \<and> (\<exists>x. (\<exists>p\<in>{[], [[Tick]\<^sub>E]}. \<exists>q\<in>{x. [X2]\<^sub>R # [Tock]\<^sub>E # x \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma>' @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)} = {}"
        by (smt disjoint disjoint_iff_not_equal subsetCE)
      then have "\<exists>x. (\<exists>p\<in>{[], [[Tick]\<^sub>E]}. \<exists>q\<in>{x. [X2]\<^sub>R # [Tock]\<^sub>E # x \<in> Q}. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<sigma>' @ [Xa \<union> Y]\<^sub>R # \<sigma> \<in> x"
        using 1 2 3 4 6 p_P q_Q case_assms induction_hypothesis[where P="{[], [[Tick]\<^sub>E]}", where Q="{x. [X2]\<^sub>R # [Tock]\<^sub>E # x \<in> Q}"] by fastforce
      then obtain qa where "qa \<in> {x. [X2]\<^sub>R # [Tock]\<^sub>E # x \<in> Q}" "\<sigma>' @ [Xa \<union> Y]\<^sub>R # \<sigma> \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C qa"
        by (auto, metis (no_types, lifting) "1" TT1_def TT_def mem_Collect_eq merge_traces_empty_merge_traces_tick merge_traces_comm)
      then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [Xa \<union> Y]\<^sub>R # \<sigma> \<in> x"
        using case_assms p_P apply (rule_tac x="([[Tick]\<^sub>E]) \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([X2]\<^sub>R # [Tock]\<^sub>E # qa)" in exI, simp_all)
        by (rule_tac x="[[Tick]\<^sub>E]" in bexI, rule_tac x="([X2]\<^sub>R # [Tock]\<^sub>E # qa)" in bexI, simp_all)
    qed
  next
    fix va P Q X Y p q
    assume "TT P" "TT Q" "[Tock]\<^sub>E # va @ [X]\<^sub>R # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "p \<in> P" "q \<in> Q"
    then have "ttWF ([Tock]\<^sub>E # va @ [X]\<^sub>R # \<sigma>)"
      using TT_wf merge_traces_wf by blast
    then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Tock]\<^sub>E # va @ [X \<union> Y]\<^sub>R # \<sigma> \<in> x"
      by auto
  next
    fix v vc P Q X Y p q
    assume "TT P" "TT Q" "[Tock]\<^sub>E # v # vc @ [X]\<^sub>R # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "p \<in> P" "q \<in> Q"
    then have "ttWF ([Tock]\<^sub>E # v # vc @ [X]\<^sub>R # \<sigma>)"
      using TT_wf merge_traces_wf by blast
    then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Tock]\<^sub>E # v # vc @ [X \<union> Y]\<^sub>R # \<sigma> \<in> x"
      by auto
  next
    fix v vc P Q X Y p q
    assume "TT P" "TT Q" "[Tock]\<^sub>E # v # vc @ [X]\<^sub>R # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "p \<in> P" "q \<in> Q"
    then have "ttWF ([Tock]\<^sub>E # v # vc @ [X]\<^sub>R # \<sigma>)"
      using TT_wf merge_traces_wf by blast
    then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Tock]\<^sub>E # v # vc @ [X \<union> Y]\<^sub>R # \<sigma> \<in> x"
      by auto
  next
    fix v vc P Q X Y p q
    assume "TT P" "TT Q" "[Tick]\<^sub>E # v # vc @ [X]\<^sub>R # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "p \<in> P" "q \<in> Q"
    then have "ttWF ([Tick]\<^sub>E # v # vc @ [X]\<^sub>R # \<sigma>)"
      using TT_wf merge_traces_wf by blast
    then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Tick]\<^sub>E # v # vc @ [X \<union> Y]\<^sub>R # \<sigma> \<in> x"
      by auto
  next
    fix v vc P Q X Y p q
    assume "TT P" "TT Q" "[Tick]\<^sub>E # v # vc @ [X]\<^sub>R # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "p \<in> P" "q \<in> Q"
    then have "ttWF ([Tick]\<^sub>E # v # vc @ [X]\<^sub>R # \<sigma>)"
      using TT_wf merge_traces_wf by blast
    then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Tick]\<^sub>E # v # vc @ [X \<union> Y]\<^sub>R # \<sigma> \<in> x"
      by auto
  next
    fix va vd vc P Q X Y p q
    assume "TT P" "TT Q" "[va]\<^sub>R # [Event vd]\<^sub>E # vc @ [X]\<^sub>R # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "p \<in> P" "q \<in> Q"
    then have "ttWF ([va]\<^sub>R # [Event vd]\<^sub>E # vc @ [X]\<^sub>R # \<sigma>)"
      using TT_wf merge_traces_wf by blast
    then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [va]\<^sub>R # [Event vd]\<^sub>E # vc @ [X \<union> Y]\<^sub>R # \<sigma> \<in> x"
      by auto
  next
    fix va vc P Q X Y p q
    assume "TT P" "TT Q" "[va]\<^sub>R # [Tick]\<^sub>E # vc @ [X]\<^sub>R # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "p \<in> P" "q \<in> Q"
    then have "ttWF ([va]\<^sub>R # [Tick]\<^sub>E # vc @ [X]\<^sub>R # \<sigma>)"
      using TT_wf merge_traces_wf by blast
    then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [va]\<^sub>R # [Tick]\<^sub>E # vc @ [X \<union> Y]\<^sub>R # \<sigma> \<in> x"
      by auto
  next
    fix va v vc P Q X Y p q
    assume "TT P" "TT Q" "[va]\<^sub>R # [v]\<^sub>R # vc @ [X]\<^sub>R # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "p \<in> P" "q \<in> Q"
    then have "ttWF ([va]\<^sub>R # [v]\<^sub>R # vc @ [X]\<^sub>R # \<sigma>)"
      using TT_wf merge_traces_wf by blast
    then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [va]\<^sub>R # [v]\<^sub>R # vc @ [X \<union> Y]\<^sub>R # \<sigma> \<in> x"
      by auto
  qed
  then show "\<And>X Y p q.
       Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<rho> @ [[e]\<^sub>E] \<in> x) \<or>
                e = Tock \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> x)} = {} \<Longrightarrow>
       \<rho> @ [X]\<^sub>R # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> p \<in> P \<Longrightarrow> q \<in> Q \<Longrightarrow> \<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> x"
    using assms by auto
qed

lemma merge_traces_end_event:
  shows "\<And> p q. ttWF p \<Longrightarrow> ttWF q \<Longrightarrow> e \<notin> A \<Longrightarrow> \<rho> @ [[Event e]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> 
    (\<exists> p'. p' \<lesssim>\<^sub>C p \<and> ttWF (p' @ [[Event e]\<^sub>E]) \<and> \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<or> (\<exists> q'. q' \<lesssim>\<^sub>C q \<and> ttWF (q' @ [[Event e]\<^sub>E]) \<and> \<rho> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
proof (induct \<rho> rule:ttWF.induct, auto)
  fix p q
  assume assm1: "e \<notin> A"
  show "[[Event e]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> 
     \<forall>q'. ttWF (q' @ [[Event e]\<^sub>E]) \<longrightarrow> q' \<lesssim>\<^sub>C q \<longrightarrow> [] \<notin> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q' \<Longrightarrow>
     \<exists>p'. p' \<lesssim>\<^sub>C p \<and> ttWF (p' @ [[Event e]\<^sub>E]) \<and> [] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
  proof (cases "(p, q)" rule:ttWF2.cases, simp_all)
    fix f \<sigma>
    assume "\<forall>q'. ttWF (q' @ [[Event f]\<^sub>E]) \<longrightarrow> q' \<lesssim>\<^sub>C [Event f]\<^sub>E # \<sigma> \<longrightarrow> [] \<notin> [] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'"
    then show "\<exists>p'. p' \<lesssim>\<^sub>C [] \<and> ttWF (p' @ [[Event f]\<^sub>E]) \<and> [] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event f]\<^sub>E # \<sigma>"
      by (erule_tac x="[]" in allE, simp)
  next
    fix X f \<sigma>
    assume "\<forall>q'. ttWF (q' @ [[Event f]\<^sub>E]) \<longrightarrow> q' \<lesssim>\<^sub>C [Event f]\<^sub>E # \<sigma> \<longrightarrow> [] \<notin> [[X]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'"
    then show "\<exists>p'. p' \<lesssim>\<^sub>C [[X]\<^sub>R] \<and> ttWF (p' @ [[Event f]\<^sub>E]) \<and> [] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event f]\<^sub>E # \<sigma>"
      by (erule_tac x="[]" in allE, simp)
  next
    fix f \<sigma>
    assume "\<forall>q'. ttWF (q' @ [[Event f]\<^sub>E]) \<longrightarrow> q' \<lesssim>\<^sub>C [Event f]\<^sub>E # \<sigma> \<longrightarrow> [] \<notin> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'"
    then show "\<exists>p'. p' \<lesssim>\<^sub>C [[Tick]\<^sub>E] \<and> ttWF (p' @ [[Event f]\<^sub>E]) \<and> [] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event f]\<^sub>E # \<sigma>"
      by (erule_tac x="[]" in allE, simp)
  next
    fix ea \<sigma>
    show "\<exists>p'. p' \<lesssim>\<^sub>C [Event ea]\<^sub>E # \<sigma> \<and> ttWF (p' @ [[Event ea]\<^sub>E]) \<and> [] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C []"
      by (rule_tac x="[]" in exI, simp)
  next
    fix ea \<sigma> Y
    show "\<exists>p'. p' \<lesssim>\<^sub>C [Event ea]\<^sub>E # \<sigma> \<and> ttWF (p' @ [[Event ea]\<^sub>E]) \<and> [] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Y]\<^sub>R]"
      by (rule_tac x="[]" in exI, simp)
  next
    fix ea \<sigma>
    show "\<exists>p'. p' \<lesssim>\<^sub>C [Event ea]\<^sub>E # \<sigma> \<and> ttWF (p' @ [[Event ea]\<^sub>E]) \<and> [] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
      by (rule_tac x="[]" in exI, simp)
  next
    fix ea \<rho> f \<sigma>
    assume "ea \<notin> A \<and> f \<notin> A \<and> ([] \<in> ([Event ea]\<^sub>E # \<rho> \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C \<sigma>) \<and> e = f \<or> [] \<in> (\<rho> \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event f]\<^sub>E # \<sigma>) \<and> e = ea) \<or>
       ea \<in> A \<and> f \<notin> A \<and> [] \<in> ([Event ea]\<^sub>E # \<rho> \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C \<sigma>) \<and> e = f \<or>
       ea \<notin> A \<and> f \<in> A \<and> [] \<in> (\<rho> \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event f]\<^sub>E # \<sigma>) \<and> e = ea \<or> ea \<in> A \<and> f \<in> A \<and> ea = f \<and> [] \<in> (\<rho> \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C \<sigma>) \<and> e = ea"
    then show "\<forall>q'. ttWF (q' @ [[Event e]\<^sub>E]) \<longrightarrow> q' \<lesssim>\<^sub>C [Event f]\<^sub>E # \<sigma> \<longrightarrow> [] \<notin> [Event ea]\<^sub>E # \<rho> \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q' \<Longrightarrow> 
      \<exists>p'. p' \<lesssim>\<^sub>C [Event ea]\<^sub>E # \<rho> \<and> ttWF (p' @ [[Event e]\<^sub>E]) \<and> [] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event f]\<^sub>E # \<sigma>"
    proof auto
      assume "[] \<in> [Event ea]\<^sub>E # \<rho> \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C \<sigma>" "ea \<notin> A"
      then show "\<exists>p'. p' \<lesssim>\<^sub>C [Event ea]\<^sub>E # \<rho> \<and> ttWF (p' @ [[Event f]\<^sub>E]) \<and> [] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event f]\<^sub>E # \<sigma>"
        by (cases \<sigma> rule:ttWF.cases,auto)
    next
      assume "[] \<in> \<rho> \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event f]\<^sub>E # \<sigma>" "f \<notin> A"
      then show "\<exists>p'. p' \<lesssim>\<^sub>C [Event ea]\<^sub>E # \<rho> \<and> ttWF (p' @ [[Event ea]\<^sub>E]) \<and> [] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event f]\<^sub>E # \<sigma>"
        by (cases \<rho> rule:ttWF.cases,auto)
    next
      assume "\<forall>q'. ttWF (q' @ [[Event f]\<^sub>E]) \<longrightarrow> q' \<lesssim>\<^sub>C [Event f]\<^sub>E # \<sigma> \<longrightarrow> [] \<notin> [Event ea]\<^sub>E # \<rho> \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'" "ea \<in> A"
      then show "\<exists>p'. p' \<lesssim>\<^sub>C [Event ea]\<^sub>E # \<rho> \<and> ttWF (p' @ [[Event f]\<^sub>E]) \<and> [] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event f]\<^sub>E # \<sigma>"
        by (erule_tac x="[]" in allE,auto)
    next
      assume "f \<in> A"
      then show "\<exists>p'. p' \<lesssim>\<^sub>C [Event ea]\<^sub>E # \<rho> \<and> ttWF (p' @ [[Event ea]\<^sub>E]) \<and> [] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event f]\<^sub>E # \<sigma>"
        by (rule_tac x="[]" in exI,auto)
    next
      assume "f \<in> A"
      then show "\<exists>p'. p' \<lesssim>\<^sub>C [Event f]\<^sub>E # \<rho> \<and> ttWF (p' @ [[Event f]\<^sub>E]) \<and> [] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event f]\<^sub>E # \<sigma>"
        by (rule_tac x="[]" in exI,auto)
    qed
  next
    fix ea \<rho> Y \<sigma>
    show "\<exists>p'. p' \<lesssim>\<^sub>C [Event ea]\<^sub>E # \<rho> \<and> ttWF (p' @ [[Event ea]\<^sub>E]) \<and> [] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>"
      by (rule_tac x="[]" in exI,auto)
  next
    fix X \<rho> f \<sigma>
    assume "\<forall>q'. ttWF (q' @ [[Event f]\<^sub>E]) \<longrightarrow> q' \<lesssim>\<^sub>C [Event f]\<^sub>E # \<sigma> \<longrightarrow> [] \<notin> [X]\<^sub>R # [Tock]\<^sub>E # \<rho> \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'"
    then show "\<exists>p'. p' \<lesssim>\<^sub>C [X]\<^sub>R # [Tock]\<^sub>E # \<rho> \<and> ttWF (p' @ [[Event f]\<^sub>E]) \<and> [] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event f]\<^sub>E # \<sigma>"
      by (erule_tac x="[]" in allE,auto)
  qed
next
  fix X p q
  assume "[[X]\<^sub>R, [Event e]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "ttWF p" "ttWF q"
  then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> ttWF (p' @ [[Event e]\<^sub>E]) \<and> [[X]\<^sub>R] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    by (meson ttWF.simps merge_traces_wf)
next
  fix p q
  assume "[[Tick]\<^sub>E, [Event e]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "ttWF p" "ttWF q"
  then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> ttWF (p' @ [[Event e]\<^sub>E]) \<and> [[Tick]\<^sub>E] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    by (meson ttWF.simps merge_traces_wf)
next
  fix ea \<sigma> 
  fix p q :: "'a ttobs list"
  assume p_wf: "ttWF p"
  assume q_wf: "ttWF q"
  assume assm1: "\<And>p q. ttWF p \<Longrightarrow> ttWF q \<Longrightarrow> \<sigma> @ [[Event e]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> 
    (\<exists>p'. p' \<lesssim>\<^sub>C p \<and> ttWF (p' @ [[Event e]\<^sub>E]) \<and> \<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) 
      \<or> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> ttWF (q' @ [[Event e]\<^sub>E]) \<and> \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
  assume assm2: "[Event ea]\<^sub>E # \<sigma> @ [[Event e]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
  then have "\<exists> p' q'. \<sigma> @ [[Event e]\<^sub>E] \<in> (p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q') \<and> ttWF p' \<and> ttWF q'
    \<and> ((ea \<in> A \<and> p = [Event ea]\<^sub>E # p' \<and> q = [Event ea]\<^sub>E # q')
      \<or> (ea \<notin> A \<and> ((p = [Event ea]\<^sub>E # p' \<and> q = q') \<or> (p = p' \<and> q = [Event ea]\<^sub>E # q'))))"
  proof (cases "(p, q)" rule:ttWF2.cases, auto)
    fix \<sigma>'
    assume "q = [Event ea]\<^sub>E # \<sigma>'"
    then show "ttWF \<sigma>'"
      using q_wf by auto
  next
    fix X \<sigma>'
    assume "q = [Event ea]\<^sub>E # \<sigma>'"
    then show "ttWF \<sigma>'"
      using q_wf by auto
  next
    fix \<sigma>'
    assume "q = [Event ea]\<^sub>E # \<sigma>'"
    then show "ttWF \<sigma>'"
      using q_wf by auto
  next
    fix \<sigma>'
    assume "p = [Event ea]\<^sub>E # \<sigma>'"
    then show "ttWF \<sigma>'"
      using p_wf by auto
  next
    fix \<sigma>' Y
    assume "p = [Event ea]\<^sub>E # \<sigma>'"
    then show "ttWF \<sigma>'"
      using p_wf by auto
  next
    fix \<sigma>' Y
    assume "p = [Event ea]\<^sub>E # \<sigma>'"
    then show "ttWF \<sigma>'"
      using p_wf by auto
  next
    fix eb \<rho> \<sigma>'
    assume "q = [Event ea]\<^sub>E # \<sigma>'"
    then have \<sigma>'_wf: "ttWF \<sigma>'"
      using q_wf by auto
    assume "p = [Event eb]\<^sub>E # \<rho>"
    then show "\<sigma> @ [[Event e]\<^sub>E] \<in> [Event eb]\<^sub>E # \<rho> \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C \<sigma>' \<Longrightarrow>
       \<exists>p' q'. \<sigma> @ [[Event e]\<^sub>E] \<in> (p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q') \<and>
               ttWF p' \<and> ttWF q' \<and> (eb = ea \<and> \<rho> = p' \<and> [Event ea]\<^sub>E # \<sigma>' = q' \<or> [Event eb]\<^sub>E # \<rho> = p' \<and> \<sigma>' = q')"
      using p_wf \<sigma>'_wf by (rule_tac x="[Event eb]\<^sub>E # \<rho>" in exI, rule_tac x="\<sigma>'" in exI, simp)
  next
    fix f \<rho> \<sigma>'
    assume "p = [Event ea]\<^sub>E # \<rho>"
    then have \<rho>_wf: "ttWF \<rho>"
      using p_wf by auto
    assume "q = [Event f]\<^sub>E # \<sigma>'"
    then show "\<sigma> @ [[Event e]\<^sub>E] \<in> \<rho> \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event f]\<^sub>E # \<sigma>' \<Longrightarrow> 
      \<exists>p' q'. \<sigma> @ [[Event e]\<^sub>E] \<in> (p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q') \<and>
                      ttWF p' \<and> ttWF q' \<and> (\<rho> = p' \<and> [Event f]\<^sub>E # \<sigma>' = q' \<or> [Event ea]\<^sub>E # \<rho> = p' \<and> f = ea \<and> \<sigma>' = q')"
      using q_wf \<rho>_wf by (rule_tac x="\<rho>" in exI, rule_tac x="[Event f]\<^sub>E # \<sigma>'" in exI, simp)
  next
    fix eb \<rho> \<sigma>'
    assume "q = [Event ea]\<^sub>E # \<sigma>'"
    then have \<sigma>'_wf: "ttWF \<sigma>'"
      using q_wf by auto
    assume "p = [Event eb]\<^sub>E # \<rho>"
    then show "\<sigma> @ [[Event e]\<^sub>E] \<in> [Event eb]\<^sub>E # \<rho> \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C \<sigma>' \<Longrightarrow> 
      \<exists>p' q'. \<sigma> @ [[Event e]\<^sub>E] \<in> (p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q') \<and>
               ttWF p' \<and> ttWF q' \<and> (eb = ea \<and> \<rho> = p' \<and> [Event ea]\<^sub>E # \<sigma>' = q' \<or> [Event eb]\<^sub>E # \<rho> = p' \<and> \<sigma>' = q')"
      using p_wf \<sigma>'_wf by (rule_tac x="[Event eb]\<^sub>E # \<rho>" in exI, rule_tac x="\<sigma>'" in exI, simp)
  next
    fix f \<rho> \<sigma>'
    assume "p = [Event ea]\<^sub>E # \<rho>"
    then have \<rho>_wf: "ttWF \<rho>"
      using p_wf by auto
    assume "q = [Event f]\<^sub>E # \<sigma>'"
    then show "\<sigma> @ [[Event e]\<^sub>E] \<in> \<rho> \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event f]\<^sub>E # \<sigma>' \<Longrightarrow>
      \<exists>p' q'. \<sigma> @ [[Event e]\<^sub>E] \<in> (p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q') \<and>
                      ttWF p' \<and> ttWF q' \<and> (\<rho> = p' \<and> [Event f]\<^sub>E # \<sigma>' = q' \<or> [Event ea]\<^sub>E # \<rho> = p' \<and> f = ea \<and> \<sigma>' = q')"
      using q_wf \<rho>_wf by (rule_tac x="\<rho>" in exI, rule_tac x="[Event f]\<^sub>E # \<sigma>'" in exI, simp)
  next
    fix \<rho> \<sigma>'
    assume "p = [Event ea]\<^sub>E # \<rho>"
    then show "ttWF \<rho>"
      using p_wf by auto
  next
    fix \<rho> \<sigma>'
    assume "q = [Event ea]\<^sub>E # \<sigma>'"
    then show "ttWF \<sigma>'"
      using q_wf by auto
  next
    fix \<rho> Y \<sigma>'
    assume "p = [Event ea]\<^sub>E # \<rho>"
    then show "ttWF \<rho>"
      using p_wf by auto
  next
    fix \<rho> \<sigma>'
    assume "q = [Event ea]\<^sub>E # \<sigma>'"
    then show "ttWF \<sigma>'"
      using q_wf by auto
  next
    fix \<rho> X \<sigma>'
    assume "p = [X]\<^sub>R # [Tock]\<^sub>E # \<rho>"
    then show "ttWF \<rho>"
      using p_wf by auto
  next
    fix \<rho> Y \<sigma>'
    assume "q = [Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>'"
    then show "ttWF \<sigma>'"
      using q_wf by auto
  qed
  then obtain p' q' where p'_q'_assms: "\<sigma> @ [[Event e]\<^sub>E] \<in> (p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q') \<and> ttWF p' \<and> ttWF q' \<and>
    (ea \<in> A \<and> p = [Event ea]\<^sub>E # p' \<and> q = [Event ea]\<^sub>E # q' \<or>
           ea \<notin> A \<and> (p = [Event ea]\<^sub>E # p' \<and> q = q' \<or> p = p' \<and> q = [Event ea]\<^sub>E # q'))"
    by auto
  then have "(\<exists>p''. p'' \<lesssim>\<^sub>C p' \<and> ttWF (p'' @ [[Event e]\<^sub>E]) \<and> \<sigma> \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q') \<or> (\<exists>q''. q'' \<lesssim>\<^sub>C q' \<and> ttWF (q'' @ [[Event e]\<^sub>E]) \<and> \<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'')"
    using assm1 by auto

  then show "\<forall>q'. ttWF (q' @ [[Event e]\<^sub>E]) \<longrightarrow> q' \<lesssim>\<^sub>C q \<longrightarrow> [Event ea]\<^sub>E # \<sigma> \<notin> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q' \<Longrightarrow>
    \<exists>p'. p' \<lesssim>\<^sub>C p \<and> ttWF (p' @ [[Event e]\<^sub>E]) \<and> [Event ea]\<^sub>E # \<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    using p'_q'_assms
  proof auto
    fix p''
    assume case_assms: "\<sigma> \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'" "ea \<in> A" "p'' \<lesssim>\<^sub>C p'" "ttWF (p'' @ [[Event e]\<^sub>E])"
    then show "\<exists>p'a. p'a \<lesssim>\<^sub>C [Event ea]\<^sub>E # p' \<and> ttWF (p'a @ [[Event e]\<^sub>E]) \<and> [Event ea]\<^sub>E # \<sigma> \<in> p'a \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event ea]\<^sub>E # q'"
      by (rule_tac x="[Event ea]\<^sub>E # p''" in exI, auto)
  next
    fix p''
    assume case_assms: "\<sigma> \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'" "ea \<notin> A" "p'' \<lesssim>\<^sub>C p'" "ttWF (p'' @ [[Event e]\<^sub>E])"
    then show "\<exists>p'a. p'a \<lesssim>\<^sub>C [Event ea]\<^sub>E # p' \<and> ttWF (p'a @ [[Event e]\<^sub>E]) \<and> [Event ea]\<^sub>E # \<sigma> \<in> p'a \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'"
      by (rule_tac x="[Event ea]\<^sub>E # p''" in exI, auto, cases q' rule:ttWF.cases, auto)
  next
    fix p''
    assume case_assms: "\<sigma> \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'" "ea \<notin> A" "p'' \<lesssim>\<^sub>C p'" "ttWF (p'' @ [[Event e]\<^sub>E])"
    then show "\<exists>p'a. p'a \<lesssim>\<^sub>C p' \<and> ttWF (p'a @ [[Event e]\<^sub>E]) \<and> [Event ea]\<^sub>E # \<sigma> \<in> p'a \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event ea]\<^sub>E # q'"
      by (rule_tac x="p''" in exI, auto, cases p'' rule:ttWF.cases, auto)
  next
    fix q''
    assume case_assms: "\<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q''" "ea \<in> A" "q'' \<lesssim>\<^sub>C q'" "ttWF (q'' @ [[Event e]\<^sub>E])"
    then show " \<forall>q'a. ttWF (q'a @ [[Event e]\<^sub>E]) \<longrightarrow> q'a \<lesssim>\<^sub>C [Event ea]\<^sub>E # q' \<longrightarrow> [Event ea]\<^sub>E # \<sigma> \<notin> [Event ea]\<^sub>E # p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'a \<Longrightarrow>
      \<exists>p'a. p'a \<lesssim>\<^sub>C [Event ea]\<^sub>E # p' \<and> ttWF (p'a @ [[Event e]\<^sub>E]) \<and> [Event ea]\<^sub>E # \<sigma> \<in> p'a \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event ea]\<^sub>E # q'"
      by (erule_tac x="[Event ea]\<^sub>E # q''" in allE, auto)
  next
    fix q''
    assume case_assms: "\<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q''" "ea \<notin> A" "q'' \<lesssim>\<^sub>C q'" "ttWF (q'' @ [[Event e]\<^sub>E])"
    then show "\<forall>q'a. ttWF (q'a @ [[Event e]\<^sub>E]) \<longrightarrow> q'a \<lesssim>\<^sub>C q' \<longrightarrow> [Event ea]\<^sub>E # \<sigma> \<notin> [Event ea]\<^sub>E # p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'a \<Longrightarrow>
      \<exists>p'a. p'a \<lesssim>\<^sub>C [Event ea]\<^sub>E # p' \<and> ttWF (p'a @ [[Event e]\<^sub>E]) \<and> [Event ea]\<^sub>E # \<sigma> \<in> p'a \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'"
      by (erule_tac x="q''" in allE, auto, cases q'' rule:ttWF.cases, auto)
  next
    fix q''
    assume case_assms: "\<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q''" "ea \<notin> A" "q'' \<lesssim>\<^sub>C q'" "ttWF (q'' @ [[Event e]\<^sub>E])"
    then show "\<forall>q'a. ttWF (q'a @ [[Event e]\<^sub>E]) \<longrightarrow> q'a \<lesssim>\<^sub>C [Event ea]\<^sub>E # q' \<longrightarrow> [Event ea]\<^sub>E # \<sigma> \<notin> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'a \<Longrightarrow>
      \<exists>p'a. p'a \<lesssim>\<^sub>C p' \<and> ttWF (p'a @ [[Event e]\<^sub>E]) \<and> [Event ea]\<^sub>E # \<sigma> \<in> p'a \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event ea]\<^sub>E # q'"
      by (erule_tac x="[Event ea]\<^sub>E # q''" in allE, auto, cases p' rule:ttWF.cases, auto)
  qed
next
  fix X \<sigma>
  fix p q :: "'a ttobs list"
  assume p_wf: "ttWF p"
  assume q_wf: "ttWF q"
  assume assm1: "(\<And>p q. ttWF p \<Longrightarrow> ttWF q \<Longrightarrow> \<sigma> @ [[Event e]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> 
    (\<exists>p'. p' \<lesssim>\<^sub>C p \<and> ttWF (p' @ [[Event e]\<^sub>E]) \<and> \<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<or> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> ttWF (q' @ [[Event e]\<^sub>E]) \<and> \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'))"
  assume assm2: "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma> @ [[Event e]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
  then have "\<exists> p' q' X1 X2. \<sigma> @ [[Event e]\<^sub>E] \<in> (p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q') \<and> 
    (p = [X1]\<^sub>R # [Tock]\<^sub>E # p' \<and> q = [X2]\<^sub>R # [Tock]\<^sub>E # q'
      \<or> p = [X1]\<^sub>R # [Tock]\<^sub>E # p' \<and> q = q' \<and> q = [[Tick]\<^sub>E]
      \<or> q = [X2]\<^sub>R # [Tock]\<^sub>E # q' \<and> p = p' \<and> p = [[Tick]\<^sub>E])"
    by (auto, induct p q rule:ttWF2.induct, simp_all)
  then obtain p' q' X1 X2 where p'_q'_assms: "\<sigma> @ [[Event e]\<^sub>E] \<in> (p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q') \<and>
     (p = [X1]\<^sub>R # [Tock]\<^sub>E # p' \<and> q = [X2]\<^sub>R # [Tock]\<^sub>E # q' \<or>
      p = [X1]\<^sub>R # [Tock]\<^sub>E # p' \<and> q = q' \<and> q = [[Tick]\<^sub>E] \<or> q = [X2]\<^sub>R # [Tock]\<^sub>E # q' \<and> p = p' \<and> p = [[Tick]\<^sub>E])"
    by auto
  then have "(\<exists>p''. p'' \<lesssim>\<^sub>C p' \<and> ttWF (p'' @ [[Event e]\<^sub>E]) \<and> \<sigma> \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')
    \<or> (\<exists>q''. q'' \<lesssim>\<^sub>C q' \<and> ttWF (q'' @ [[Event e]\<^sub>E]) \<and> \<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'')"
    using p_wf q_wf assm1
  proof auto
    assume "ttWF p'" "ttWF q'" "\<sigma> @ [[Event e]\<^sub>E] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'"
    and "\<And>p q. ttWF p \<Longrightarrow> ttWF q \<Longrightarrow> \<sigma> @ [[Event e]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow>
      (\<exists>p'. p' \<lesssim>\<^sub>C p \<and> ttWF (p' @ [[Event e]\<^sub>E]) \<and> \<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<or> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> ttWF (q' @ [[Event e]\<^sub>E]) \<and> \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
    then have "(\<exists>p''. p'' \<lesssim>\<^sub>C p' \<and> ttWF (p'' @ [[Event e]\<^sub>E]) \<and> \<sigma> \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q') \<or> (\<exists>q''. q'' \<lesssim>\<^sub>C q' \<and> ttWF (q'' @ [[Event e]\<^sub>E]) \<and> \<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'')"
      by auto
    then show "\<forall>q''. ttWF (q'' @ [[Event e]\<^sub>E]) \<longrightarrow> q'' \<lesssim>\<^sub>C q' \<longrightarrow> \<sigma> \<notin> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'' \<Longrightarrow>
      q = [X2]\<^sub>R # [Tock]\<^sub>E # q' \<Longrightarrow> p = [X1]\<^sub>R # [Tock]\<^sub>E # p' \<Longrightarrow> \<exists>p''. p'' \<lesssim>\<^sub>C p' \<and> ttWF (p'' @ [[Event e]\<^sub>E]) \<and> \<sigma> \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'"
      by auto
  next
    assume "ttWF p'" "\<sigma> @ [[Event e]\<^sub>E] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" "q' = [[Tick]\<^sub>E]"
    and "\<And>p q. ttWF p \<Longrightarrow> ttWF q \<Longrightarrow> \<sigma> @ [[Event e]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow>
      (\<exists>p'. p' \<lesssim>\<^sub>C p \<and> ttWF (p' @ [[Event e]\<^sub>E]) \<and> \<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<or> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> ttWF (q' @ [[Event e]\<^sub>E]) \<and> \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
    then have "(\<exists>p''. p'' \<lesssim>\<^sub>C p' \<and> ttWF (p'' @ [[Event e]\<^sub>E]) \<and> \<sigma> \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q') \<or> (\<exists>q''. q'' \<lesssim>\<^sub>C q' \<and> ttWF (q'' @ [[Event e]\<^sub>E]) \<and> \<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'')"
      by auto
    then show "\<forall>q''. ttWF (q'' @ [[Event e]\<^sub>E]) \<longrightarrow> q'' \<lesssim>\<^sub>C [[Tick]\<^sub>E] \<longrightarrow> \<sigma> \<notin> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'' \<Longrightarrow>
      p = [X1]\<^sub>R # [Tock]\<^sub>E # p' \<Longrightarrow> q = [[Tick]\<^sub>E] \<Longrightarrow> q' = [[Tick]\<^sub>E] \<Longrightarrow> 
      \<exists>p''. p'' \<lesssim>\<^sub>C p' \<and> ttWF (p'' @ [[Event e]\<^sub>E]) \<and> \<sigma> \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
      by auto
  next
    assume "ttWF q'" "\<sigma> @ [[Event e]\<^sub>E] \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'" "p' = [[Tick]\<^sub>E]"
    and "\<And>p q. ttWF p \<Longrightarrow> ttWF q \<Longrightarrow> \<sigma> @ [[Event e]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow>
      (\<exists>p'. p' \<lesssim>\<^sub>C p \<and> ttWF (p' @ [[Event e]\<^sub>E]) \<and> \<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<or> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> ttWF (q' @ [[Event e]\<^sub>E]) \<and> \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
    then have "(\<exists>p''. p'' \<lesssim>\<^sub>C p' \<and> ttWF (p'' @ [[Event e]\<^sub>E]) \<and> \<sigma> \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q') \<or> (\<exists>q''. q'' \<lesssim>\<^sub>C q' \<and> ttWF (q'' @ [[Event e]\<^sub>E]) \<and> \<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'')"
      by auto
    then show "\<forall>q''. ttWF (q'' @ [[Event e]\<^sub>E]) \<longrightarrow> q'' \<lesssim>\<^sub>C q' \<longrightarrow> \<sigma> \<notin> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'' \<Longrightarrow>
      q = [X2]\<^sub>R # [Tock]\<^sub>E # q' \<Longrightarrow>  p = [[Tick]\<^sub>E] \<Longrightarrow> p' = [[Tick]\<^sub>E] \<Longrightarrow> 
      \<exists>p''. p'' \<lesssim>\<^sub>C [[Tick]\<^sub>E] \<and> ttWF (p'' @ [[Event e]\<^sub>E]) \<and> \<sigma> \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'"
      by auto
  qed
  then show "\<forall>q'. ttWF (q' @ [[Event e]\<^sub>E]) \<longrightarrow> q' \<lesssim>\<^sub>C q \<longrightarrow> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<notin> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q' \<Longrightarrow>
       \<exists>p'. p' \<lesssim>\<^sub>C p \<and> ttWF (p' @ [[Event e]\<^sub>E]) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    using p'_q'_assms
  proof auto
    fix p''
    assume "q = [X2]\<^sub>R # [Tock]\<^sub>E # q'" " p = [X1]\<^sub>R # [Tock]\<^sub>E # p'" "\<sigma> \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'" "p'' \<lesssim>\<^sub>C p'" "ttWF (p'' @ [[Event e]\<^sub>E])"
    then show "\<exists>p'a. p'a \<lesssim>\<^sub>C [X1]\<^sub>R # [Tock]\<^sub>E # p' \<and> ttWF (p'a @ [[Event e]\<^sub>E]) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> p'a \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [X2]\<^sub>R # [Tock]\<^sub>E # q'"
      using assm2 by (rule_tac x="[X1]\<^sub>R # [Tock]\<^sub>E # p''" in exI, simp_all)
  next
    fix p''
    assume "q = [[Tick]\<^sub>E]" " p = [X1]\<^sub>R # [Tock]\<^sub>E # p'" "\<sigma> \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" "p'' \<lesssim>\<^sub>C p'" "ttWF (p'' @ [[Event e]\<^sub>E])"
    then show "\<exists>p'a. p'a \<lesssim>\<^sub>C [X1]\<^sub>R # [Tock]\<^sub>E # p' \<and> ttWF (p'a @ [[Event e]\<^sub>E]) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> p'a \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
      using assm2 by (rule_tac x="[X1]\<^sub>R # [Tock]\<^sub>E # p''" in exI, simp_all)
  next
    fix p''
    assume case_assms: "p = [[Tick]\<^sub>E]" " q = [X2]\<^sub>R # [Tock]\<^sub>E # q'" "\<sigma> \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'" "p'' \<lesssim>\<^sub>C [[Tick]\<^sub>E]" "ttWF (p'' @ [[Event e]\<^sub>E])"
    then have "p'' = [] \<or> p'' = [[Tick]\<^sub>E]"
      by (cases p'' rule:ttWF.cases, auto)
    then show "\<exists>p'. p' \<lesssim>\<^sub>C [[Tick]\<^sub>E] \<and> ttWF (p' @ [[Event e]\<^sub>E]) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [X2]\<^sub>R # [Tock]\<^sub>E # q'"
      using assm2 case_assms
    proof (rule_tac x="p''" in exI, simp_all, safe, simp_all)
      have "\<And>\<sigma>. \<sigma> \<in> [] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q' \<Longrightarrow> \<sigma> @ [[Event e]\<^sub>E] \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q' \<Longrightarrow> False"
        by (induct q' rule:ttWF.induct, simp_all, safe, simp, blast)
      then show "\<sigma> \<in> [] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q' \<Longrightarrow> \<sigma> @ [[Event e]\<^sub>E] \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q' \<Longrightarrow> False"
        by auto
    qed
  next
    fix q''
    assume "q = [X2]\<^sub>R # [Tock]\<^sub>E # q'" " p = [X1]\<^sub>R # [Tock]\<^sub>E # p'" "\<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q''" "q'' \<lesssim>\<^sub>C q'" "ttWF (q'' @ [[Event e]\<^sub>E])"
    then show "\<forall>q'a. ttWF (q'a @ [[Event e]\<^sub>E]) \<longrightarrow> q'a \<lesssim>\<^sub>C [X2]\<^sub>R # [Tock]\<^sub>E # q' \<longrightarrow> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<notin> [X1]\<^sub>R # [Tock]\<^sub>E # p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'a \<Longrightarrow>
      \<exists>p'a. p'a \<lesssim>\<^sub>C [X1]\<^sub>R # [Tock]\<^sub>E # p' \<and> ttWF (p'a @ [[Event e]\<^sub>E]) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> p'a \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [X2]\<^sub>R # [Tock]\<^sub>E # q'"
      using assm2 by (erule_tac x="[X2]\<^sub>R # [Tock]\<^sub>E # q''" in allE, simp_all)
  next
    fix q''
    assume case_assms: "q = [[Tick]\<^sub>E]" " p = [X1]\<^sub>R # [Tock]\<^sub>E # p'" "\<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q''" "q'' \<lesssim>\<^sub>C [[Tick]\<^sub>E]" "ttWF (q'' @ [[Event e]\<^sub>E])"
    then have "q'' = [] \<or> q'' = [[Tick]\<^sub>E]"
      by (cases q'' rule:ttWF.cases, auto)
    then show "\<forall>q'. ttWF (q' @ [[Event e]\<^sub>E]) \<longrightarrow> q' \<lesssim>\<^sub>C [[Tick]\<^sub>E] \<longrightarrow> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<notin> [X1]\<^sub>R # [Tock]\<^sub>E # p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q' \<Longrightarrow>
      \<exists>p'a. p'a \<lesssim>\<^sub>C [X1]\<^sub>R # [Tock]\<^sub>E # p' \<and> ttWF (p'a @ [[Event e]\<^sub>E]) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> p'a \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
      using assm2 case_assms
    proof (erule_tac x="q''" in allE, simp_all, safe, simp_all)
      fix Aa
      have "\<And>\<sigma>. \<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [] \<Longrightarrow> \<sigma> @ [[Event e]\<^sub>E] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E] \<Longrightarrow> False"
        by (induct p' rule:ttWF.induct, simp_all, safe, simp, blast)
      then show "\<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [] \<Longrightarrow> \<sigma> @ [[Event e]\<^sub>E] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E] \<Longrightarrow> \<exists>p'a. p'a \<lesssim>\<^sub>C [X1]\<^sub>R # [Tock]\<^sub>E # p' \<and> ttWF (p'a @ [[Event e]\<^sub>E]) \<and> [X1 \<union> Event ` Aa]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> p'a \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
        by auto
    qed
  next
    fix q''
    assume "p = [[Tick]\<^sub>E]" "q = [X2]\<^sub>R # [Tock]\<^sub>E # q'" "\<sigma> \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q''" "q'' \<lesssim>\<^sub>C q'" "ttWF (q'' @ [[Event e]\<^sub>E])"
    then show "\<forall>q'a. ttWF (q'a @ [[Event e]\<^sub>E]) \<longrightarrow> q'a \<lesssim>\<^sub>C [X2]\<^sub>R # [Tock]\<^sub>E # q' \<longrightarrow> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<notin> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'a \<Longrightarrow>
      \<exists>p'. p' \<lesssim>\<^sub>C [[Tick]\<^sub>E] \<and> ttWF (p' @ [[Event e]\<^sub>E]) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [X2]\<^sub>R # [Tock]\<^sub>E # q'"
      using assm2 by (erule_tac x="[X2]\<^sub>R # [Tock]\<^sub>E # q''" in allE, simp_all)  
  qed
next
  fix va p q
  assume "[Tock]\<^sub>E # va @ [[Event e]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "ttWF p" "ttWF q"
  then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> ttWF (p' @ [[Event e]\<^sub>E]) \<and> [Tock]\<^sub>E # va \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    by (meson ttWF.simps merge_traces_wf)
next
  fix v vc p q
  assume "[Tock]\<^sub>E # v # vc @ [[Event e]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "ttWF p" "ttWF q"
  then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> ttWF (p' @ [[Event e]\<^sub>E]) \<and> [Tock]\<^sub>E # v # vc \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    by (meson ttWF.simps merge_traces_wf)
next
  fix v vc p q
  assume "[Tick]\<^sub>E # v # vc @ [[Event e]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "ttWF p" "ttWF q"
  then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> ttWF (p' @ [[Event e]\<^sub>E]) \<and> [Tick]\<^sub>E # v # vc \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    by (meson ttWF.simps merge_traces_wf)
next
  fix vb vc p q
  assume "[Tock]\<^sub>E # vb # vc @ [[Event e]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "ttWF p" "ttWF q"
  then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> ttWF (p' @ [[Event e]\<^sub>E]) \<and> [Tock]\<^sub>E # vb # vc \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    by (meson ttWF.simps merge_traces_wf)
next
  fix vb vc p q
  assume "[Tick]\<^sub>E # vb # vc @ [[Event e]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "ttWF p" "ttWF q"
  then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> ttWF (p' @ [[Event e]\<^sub>E]) \<and> [Tick]\<^sub>E # vb # vc \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    by (meson ttWF.simps merge_traces_wf)
next
  fix va vd vc p q
  assume "[va]\<^sub>R # [Event vd]\<^sub>E # vc @ [[Event e]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "ttWF p" "ttWF q"
  then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> ttWF (p' @ [[Event e]\<^sub>E]) \<and> [va]\<^sub>R # [Event vd]\<^sub>E # vc \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    by (meson ttWF.simps merge_traces_wf)
next
  fix va vc p q
  assume "[va]\<^sub>R # [Tick]\<^sub>E # vc @ [[Event e]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "ttWF p" "ttWF q"
  then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> ttWF (p' @ [[Event e]\<^sub>E]) \<and> [va]\<^sub>R # [Tick]\<^sub>E # vc \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    by (meson ttWF.simps merge_traces_wf)
next
  fix va v vc p q
  assume "[va]\<^sub>R # [v]\<^sub>R # vc @ [[Event e]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "ttWF p" "ttWF q"
  then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> ttWF (p' @ [[Event e]\<^sub>E]) \<and> [va]\<^sub>R # [v]\<^sub>R # vc \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    by (meson ttWF.simps merge_traces_wf)
qed

lemma TT3_ParComp:
  shows "\<And> P Q. TT P \<Longrightarrow> TT Q \<Longrightarrow> TT3 (P \<lbrakk>A\<rbrakk>\<^sub>C Q)"
  unfolding ParCompTT_def TT3_def
proof auto
  fix x
  show "\<And>P Q p q. TT P \<Longrightarrow> TT Q \<Longrightarrow> p \<in> P \<Longrightarrow> q \<in> Q \<Longrightarrow> x \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> TT3_trace x"
  proof (induct x rule:ttWF.induct, auto)
    fix e \<sigma> P Q p q
    assume "[Event e]\<^sub>E # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    then have p_q_cases: "(\<exists> p' q'. p = [Event e]\<^sub>E # p' \<and> q = [Event e]\<^sub>E # q' \<and> e \<in> A \<and> \<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')
      \<or> (\<exists> p'. p = [Event e]\<^sub>E # p' \<and> e \<notin> A \<and> \<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q)
      \<or> (\<exists> q'. q = [Event e]\<^sub>E # q' \<and> e \<notin> A \<and> \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
      by (cases "(p,q)" rule:ttWF2.cases, auto)
    assume induction_hypothesis: "\<And>P Q p q. TT P \<Longrightarrow> TT Q \<Longrightarrow> p \<in> P \<Longrightarrow> q \<in> Q \<Longrightarrow> \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> TT3_trace \<sigma>"
    assume p_P: "p \<in> P" and q_Q: "q \<in> Q"
    assume TT_P: "TT P" and TT_Q: "TT Q"
    show "TT3_trace ([Event e]\<^sub>E # \<sigma>)"
      using p_q_cases
    proof auto
      fix p' q' 
      assume p_def: "p = [Event e]\<^sub>E # p'"
      assume q_def: "q = [Event e]\<^sub>E # q'"
      assume in_p'_parcomp_q': "\<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'"
      have 1: "TT {t. [Event e]\<^sub>E # t \<in> P}"
        using TT_P TT_init_event p_P p_def by force
      have 2: "TT {t. [Event e]\<^sub>E # t \<in> Q}"
        using TT_Q TT_init_event q_Q q_def by force
      have 3: "p' \<in> {t. [Event e]\<^sub>E # t \<in> P}"
        using p_def p_P by force
      have 4: "q' \<in> {t. [Event e]\<^sub>E # t \<in> Q}"
        using q_def q_Q by force
      have "TT3_trace \<sigma>"
        using induction_hypothesis 1 2 3 4 in_p'_parcomp_q' by auto
      then show "TT3_trace ([Event e]\<^sub>E # \<sigma>)"
        by (cases \<sigma>, auto)
    next
      fix p' 
      assume p_def: "p = [Event e]\<^sub>E # p'"
      assume in_p'_parcomp_q: "\<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
      have 1: "TT {t. [Event e]\<^sub>E # t \<in> P}"
        using TT_P TT_init_event p_P p_def by force
      have 2: "p' \<in> {t. [Event e]\<^sub>E # t \<in> P}"
        using p_def p_P by force
      have "TT3_trace \<sigma>"
        using induction_hypothesis 1 2 TT_Q q_Q in_p'_parcomp_q by auto
      then show "TT3_trace ([Event e]\<^sub>E # \<sigma>)"
        by (cases \<sigma>, auto)
    next
      fix q' 
      assume q_def: "q = [Event e]\<^sub>E # q'"
      assume in_p_parcomp_q': "\<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'"
      have 1: "TT {t. [Event e]\<^sub>E # t \<in> Q}"
        using TT_Q TT_init_event q_Q q_def by force
      have 2: "q' \<in> {t. [Event e]\<^sub>E # t \<in> Q}"
        using q_def q_Q by force
      have "TT3_trace \<sigma>"
        using induction_hypothesis 1 2 TT_P p_P in_p_parcomp_q' by auto
      then show "TT3_trace ([Event e]\<^sub>E # \<sigma>)"
        by (cases \<sigma>, auto)
    qed
  next
    fix X \<sigma> P Q p q
    assume "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    then have p_q_cases: "(\<exists> p' q' X1 X2. p = [X1]\<^sub>R # [Tock]\<^sub>E # p' \<and> q = [X2]\<^sub>R # [Tock]\<^sub>E # q' \<and> [[X]\<^sub>R] \<in> [[X1]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[X2]\<^sub>R])
      \<or> (\<exists> p' X1. p = [X1]\<^sub>R # [Tock]\<^sub>E # p' \<and> q = [[Tick]\<^sub>E] \<and> [[X]\<^sub>R] \<in> [[X1]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E])
      \<or> (\<exists> q' X2. q = [X2]\<^sub>R # [Tock]\<^sub>E # q' \<and> p = [[Tick]\<^sub>E] \<and> [[X]\<^sub>R] \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[X2]\<^sub>R])"
      by (cases "(p,q)" rule:ttWF2.cases, auto)
    assume p_P: "p \<in> P" and q_Q: "q \<in> Q"
    assume TT_P: "TT P" and TT_Q: "TT Q"
    show "Tock \<in> X \<Longrightarrow> False"
      using p_q_cases
    proof safe
      fix p' q' X1 X2
      assume "p = [X1]\<^sub>R # [Tock]\<^sub>E # p'"
      then have Tock_notin_X1: "Tock \<notin> X1"
        using TT3_def TT3_trace.simps(3) TT_TT3 TT_P p_P by blast
      assume "q = [X2]\<^sub>R # [Tock]\<^sub>E # q'"
      then have Tock_notin_X2: "Tock \<notin> X2"
        using TT3_def TT3_trace.simps(3) TT_TT3 TT_Q q_Q by blast
      assume "[[X]\<^sub>R] \<in> [[X1]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[X2]\<^sub>R]"
      then have "Tock \<notin> X"
        using Tock_notin_X1 Tock_notin_X2 by auto
      then show "Tock \<in> X \<Longrightarrow> False"
        by auto
    next
      fix p' X1
      assume "p = [X1]\<^sub>R # [Tock]\<^sub>E # p'"
      then have Tock_notin_X1: "Tock \<notin> X1"
        using TT3_def TT3_trace.simps(3) TT_TT3 TT_P p_P by blast
      assume "[[X]\<^sub>R] \<in> [[X1]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
      then have "Tock \<notin> X"
        using Tock_notin_X1 by auto
      then show "Tock \<in> X \<Longrightarrow> False"
        by auto
    next
      fix p' q' X1 X2
      assume "q = [X2]\<^sub>R # [Tock]\<^sub>E # q'"
      then have Tock_notin_X2: "Tock \<notin> X2"
        using TT3_def TT3_trace.simps(3) TT_TT3 TT_Q q_Q by blast
      assume "[[X]\<^sub>R] \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[X2]\<^sub>R]"
      then have "Tock \<notin> X"
        using Tock_notin_X2 by auto
      then show "Tock \<in> X \<Longrightarrow> False"
        by auto
    qed
  next
    fix X \<sigma> P Q p q
    assume "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    then have p_q_cases: "(\<exists> p' q' X1 X2. p = [X1]\<^sub>R # [Tock]\<^sub>E # p' \<and> q = [X2]\<^sub>R # [Tock]\<^sub>E # q' \<and> \<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')
      \<or> (\<exists> p' X1. p = [X1]\<^sub>R # [Tock]\<^sub>E # p' \<and> q = [[Tick]\<^sub>E] \<and> \<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E])
      \<or> (\<exists> q' X2. q = [X2]\<^sub>R # [Tock]\<^sub>E # q' \<and> p = [[Tick]\<^sub>E] \<and> \<sigma> \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
      by (cases "(p,q)" rule:ttWF2.cases, auto)
    assume p_P: "p \<in> P" and q_Q: "q \<in> Q"
    assume TT_P: "TT P" and TT_Q: "TT Q"
    assume induction_hypothesis: "\<And>P Q p q. TT P \<Longrightarrow> TT Q \<Longrightarrow> p \<in> P \<Longrightarrow> q \<in> Q \<Longrightarrow> \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> TT3_trace \<sigma>"
    show "TT3_trace \<sigma>"
      using p_q_cases
    proof safe
      fix p' q' X1 X2
      assume p_def: "p = [X1]\<^sub>R # [Tock]\<^sub>E # p'"
      assume q_def: "q = [X2]\<^sub>R # [Tock]\<^sub>E # q'"
      have 1: "TT {t. [X1]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
        using TT_P TT_init_tock p_P p_def by blast
      have 2: "TT {t. [X2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}"
        using TT_Q TT_init_tock q_Q q_def by blast
      have 3: "p' \<in> {t. [X1]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
        using p_P p_def by blast
      have 4: "q' \<in> {t. [X2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}"
        using q_Q q_def by blast
      assume "\<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'"
      then show "TT3_trace \<sigma>"
        using induction_hypothesis 1 2 3 4 by auto
    next
      fix p' X1
      assume p_def: "p = [X1]\<^sub>R # [Tock]\<^sub>E # p'"
      assume q_def: "q = [[Tick]\<^sub>E]"
      have 1: "TT {t. [X1]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
        using TT_P TT_init_tock p_P p_def by blast
      have 2: "p' \<in> {t. [X1]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
        using p_P p_def by blast
      assume "\<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
      then show "TT3_trace \<sigma>"
        using induction_hypothesis 1 2 q_def q_Q TT_Q by auto
    next
      fix q' X2
      assume q_def: "q = [X2]\<^sub>R # [Tock]\<^sub>E # q'"
      assume p_def: "p = [[Tick]\<^sub>E]"
      have 1: "TT {t. [X2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}"
        using TT_Q TT_init_tock q_Q q_def by blast
      have 2: "q' \<in> {t. [X2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}"
        using q_Q q_def by blast
      assume "\<sigma> \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'"
      then show "TT3_trace \<sigma>"
        using induction_hypothesis 1 2 p_def p_P TT_P by auto
    qed
  next
    fix va P Q p q
    assume "[Tock]\<^sub>E # va \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "TT P" "TT Q" "p \<in> P" "q \<in> Q"
    then have "ttWF ([Tock]\<^sub>E # va)"
      using TT_wf merge_traces_wf by blast
    then show "TT3_trace ([Tock]\<^sub>E # va)"
      by auto
  next
    fix v vc P Q p q
    assume "[Tock]\<^sub>E # v # vc \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "TT P" "TT Q" "p \<in> P" "q \<in> Q"
    then have "ttWF ([Tock]\<^sub>E # v # vc)"
      using TT_wf merge_traces_wf by blast
    then show "TT3_trace (v # vc)"
      by auto
  next
    fix v vc P Q p q
    assume "[Tock]\<^sub>E # v # vc \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "TT P" "TT Q" "p \<in> P" "q \<in> Q"
    then have "ttWF ([Tock]\<^sub>E # v # vc)"
      using TT_wf merge_traces_wf by blast
    then show "TT3_trace (v # vc)"
      by auto
  next
    fix v vc P Q p q
    assume "[Tick]\<^sub>E # v # vc \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "TT P" "TT Q" "p \<in> P" "q \<in> Q"
    then have "ttWF ([Tick]\<^sub>E # v # vc)"
      using TT_wf merge_traces_wf by blast
    then show "TT3_trace (v # vc)"
      by auto
  next
    fix vb vc P Q p q
    assume "[Tick]\<^sub>E # vb # vc \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "TT P" "TT Q" "p \<in> P" "q \<in> Q"
    then have "ttWF ([Tick]\<^sub>E # vb # vc)"
      using TT_wf merge_traces_wf by blast
    then show "TT3_trace (vb # vc)"
      by auto
  next
    fix va vd vc P Q p q
    assume "[va]\<^sub>R # [Event vd]\<^sub>E # vc \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "TT P" "TT Q" "p \<in> P" "q \<in> Q"
    then have "ttWF ([va]\<^sub>R # [Event vd]\<^sub>E # vc)"
      using TT_wf merge_traces_wf by blast
    then show "TT3_trace ([Event vd]\<^sub>E # vc)"
      by auto
  next
    fix va vc P Q p q
    assume "[va]\<^sub>R # [Tick]\<^sub>E # vc \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "TT P" "TT Q" "p \<in> P" "q \<in> Q"
    then have "ttWF ([va]\<^sub>R # [Tick]\<^sub>E # vc)"
      using TT_wf merge_traces_wf by blast
    then show "TT3_trace ([Tick]\<^sub>E # vc)"
      by auto
  next
    fix va v vc P Q p q
    assume "[va]\<^sub>R # [v]\<^sub>R # vc \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "TT P" "TT Q" "p \<in> P" "q \<in> Q"
    then have "ttWF ([va]\<^sub>R # [v]\<^sub>R # vc)"
      using TT_wf merge_traces_wf by blast
    then show "TT3_trace ([v]\<^sub>R # vc)"
      by auto
  qed
qed

lemma TT4_init_event:
  "TT4 P \<Longrightarrow> TT4 {t. [e]\<^sub>E # t \<in> P}"
  unfolding TT4_def by (safe, force)

lemma TT1_init_event:
  assumes "TT1 P"
  shows "TT1 {t. [Event e]\<^sub>E # t \<in> P}"
  unfolding TT1_def
proof auto
  fix \<rho> \<sigma> :: "'a ttobs list"
  assume "\<rho> \<lesssim>\<^sub>C \<sigma>"
  then have "[Event e]\<^sub>E # \<rho> \<lesssim>\<^sub>C [Event e]\<^sub>E # \<sigma>"
    by auto
  then show "[Event e]\<^sub>E # \<sigma> \<in> P \<Longrightarrow> [Event e]\<^sub>E # \<rho> \<in> P"
    using TT1_def TT_TT1 assms(1) by blast
qed

lemma TT1_init_tock:
  assumes "TT1 P"
  shows "TT1 {t. [X]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
  unfolding TT1_def
proof auto
  fix \<rho> \<sigma> :: "'a ttobs list"
  assume "\<rho> \<lesssim>\<^sub>C \<sigma>"
  then have "[X]\<^sub>R # [Tock]\<^sub>E # \<rho> \<lesssim>\<^sub>C [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>"
    by auto
  also assume "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P"
  then show "[X]\<^sub>R # [Tock]\<^sub>E # \<rho> \<in> P"
    using assms(1) calculation unfolding TT_def TT1_def apply auto 
    by (erule_tac x="[X]\<^sub>R # [Tock]\<^sub>E # \<rho>" in allE, auto)
qed

lemma TT4_TT1_init_tock:
  "TT4 P \<Longrightarrow> TT1 P \<Longrightarrow> TT4 {t. [X]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
  unfolding TT4_def
proof (safe)
  fix \<rho>
  assume "\<forall>\<rho>. \<rho> \<in> P \<longrightarrow> add_Tick_refusal_trace \<rho> \<in> P" "[X]\<^sub>R # [Tock]\<^sub>E # \<rho> \<in> P"
  then have "[X \<union> {Tick}]\<^sub>R # [Tock]\<^sub>E # add_Tick_refusal_trace \<rho> \<in> P"
    by force
  also have "[X]\<^sub>R # [Tock]\<^sub>E # add_Tick_refusal_trace \<rho> \<lesssim>\<^sub>C [X \<union> {Tick}]\<^sub>R # [Tock]\<^sub>E # add_Tick_refusal_trace \<rho>"
    using tt_prefix_subset_refl by fastforce
  then show "TT1 P \<Longrightarrow> [X]\<^sub>R # [Tock]\<^sub>E # add_Tick_refusal_trace \<rho> \<in> P"
    unfolding TT1_def using calculation by blast
qed

lemma TT4_ParComp:
  assumes "TT1 P" "TT1 Q"
  assumes "TT4 P" "TT4 Q"
  shows "TT4 (P \<lbrakk>A\<rbrakk>\<^sub>C Q)"
  unfolding ParCompTT_def TT4_def using assms
proof auto
  fix \<rho>
  show "\<And> p q P Q. TT1 P \<Longrightarrow> TT1 Q \<Longrightarrow> TT4 P \<Longrightarrow> TT4 Q \<Longrightarrow> \<rho> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> p \<in> P \<Longrightarrow> q \<in> Q \<Longrightarrow>
    \<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> add_Tick_refusal_trace \<rho> \<in> x"
  proof (induct \<rho> rule:ttWF.induct, auto)
    fix X p q P Q
    assume case_assms: "[[X]\<^sub>R] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "p \<in> P" "q \<in> Q" "TT4 P" "TT4 Q"
    then have "(\<exists> Y Z. p = [[Y]\<^sub>R] \<and> q = [[Z]\<^sub>R] \<and> X \<subseteq> Y \<union> Z \<and> {e \<in> Y. e \<notin> Event ` A \<union> {Tock, Tick}} = {e \<in> Z. e \<notin> Event ` A \<union> {Tock, Tick}})
      \<or> (\<exists> Z B. p = [[Tick]\<^sub>E] \<and> q = [[Z]\<^sub>R] \<and> X = Z \<union> Event ` B \<and> B \<subseteq> A)
      \<or> (\<exists> Y B. p = [[Y]\<^sub>R] \<and> q = [[Tick]\<^sub>E] \<and> X = Y \<union> Event ` B \<and> B \<subseteq> A)"
      by (cases "(p,q)" rule:ttWF2.cases, auto)
    then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[insert Tick X]\<^sub>R] \<in> x"
    proof safe
      fix Y Z
      assume case_assms2: "p = [[Y]\<^sub>R]" "q = [[Z]\<^sub>R]" "X \<subseteq> Y \<union> Z" "{e \<in> Y. e \<notin> Event ` A \<union> {Tock, Tick}} = {e \<in> Z. e \<notin> Event ` A \<union> {Tock, Tick}}"
      then have "[[Y \<union> {Tick}]\<^sub>R] \<in> P" "[[Z \<union> {Tick}]\<^sub>R] \<in> Q"
        using TT4_def case_assms by force+
      then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[insert Tick X]\<^sub>R] \<in> x"
        using case_assms2 by (rule_tac x="[[Y \<union> {Tick}]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Z \<union> {Tick}]\<^sub>R]" in exI, safe, blast, simp, blast)
    next
      fix Z B
      assume case_assms2: "p = [[Tick]\<^sub>E]" "q = [[Z]\<^sub>R]" "B \<subseteq> A" "X = Z \<union> Event ` B"
      then have "[[Z \<union> {Tick}]\<^sub>R] \<in> Q"
        using TT4_def case_assms by force
      then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[insert Tick (Z \<union> Event ` B)]\<^sub>R] \<in> x"
        using case_assms case_assms2
        apply (rule_tac x="[[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Z \<union> {Tick}]\<^sub>R]" in exI, auto)
        by (rule_tac x="[[Tick]\<^sub>E]" in bexI, rule_tac x="[[Z \<union> {Tick}]\<^sub>R]" in bexI, auto)
    next
      fix Y B
      assume case_assms2: "p = [[Y]\<^sub>R]" "q = [[Tick]\<^sub>E]" "B \<subseteq> A" "X = Y \<union> Event ` B"
      then have "[[Y \<union> {Tick}]\<^sub>R] \<in> P"
        using TT4_def case_assms by force
      then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [[insert Tick (Y \<union> Event ` B)]\<^sub>R] \<in> x"
        using case_assms case_assms2
        apply (rule_tac x="[[Y \<union> {Tick}]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" in exI, auto)
        by (rule_tac x="[[Y \<union> {Tick}]\<^sub>R]" in bexI, rule_tac x="[[Tick]\<^sub>E]" in bexI, auto)
    qed
  next
    fix e \<sigma> p q P Q
    assume ind_hyp: "\<And>p q P Q. TT1 P \<Longrightarrow> TT1 Q \<Longrightarrow> TT4 P \<Longrightarrow> TT4 Q \<Longrightarrow> \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> p \<in> P \<Longrightarrow> q \<in> Q \<Longrightarrow>
      \<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> add_Tick_refusal_trace \<sigma> \<in> x"
    assume case_assms: "[Event e]\<^sub>E # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "p \<in> P" "q \<in> Q" "TT1 P" "TT1 Q" "TT4 P" "TT4 Q"
    then have "(\<exists> p' q'. \<sigma> \<in> (p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q') \<and> p = [Event e]\<^sub>E # p' \<and> q = [Event e]\<^sub>E # q' \<and> e \<in> A)
      \<or> (\<exists> p'. \<sigma> \<in> (p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p = [Event e]\<^sub>E # p' \<and> e \<notin> A)
      \<or> (\<exists> q'. \<sigma> \<in> (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q') \<and> q = [Event e]\<^sub>E # q' \<and> e \<notin> A)"
      by (cases "(p,q)" rule:ttWF2.cases, auto)
    then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Event e]\<^sub>E # add_Tick_refusal_trace \<sigma> \<in> x"
    proof safe
      fix p' q'
      assume case_assms2: "\<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'" "p = [Event e]\<^sub>E # p'" "q = [Event e]\<^sub>E # q'" "e \<in> A"
      have 1: "p' \<in> {t. [Event e]\<^sub>E # t \<in> P}"
        using case_assms(2) case_assms2(2) by blast
      have 2: "TT1 {t. [Event e]\<^sub>E # t \<in> P}"
        by (simp add: TT1_init_event case_assms(4))
      have 3: "TT4 {t. [Event e]\<^sub>E # t \<in> P}"
        by (simp add: TT4_init_event case_assms(6))
      have 4: "q' \<in> {t. [Event e]\<^sub>E # t \<in> Q}"
        using case_assms(3) case_assms2(3) by blast
      have 5: "TT1 {t. [Event e]\<^sub>E # t \<in> Q}"
        by (simp add: TT1_init_event case_assms(5))
      have 6: "TT4 {t. [Event e]\<^sub>E # t \<in> Q}"
        by (simp add: TT4_init_event case_assms(7))
      obtain p'' q'' where "p''\<in>{t. [Event e]\<^sub>E # t \<in> P} \<and> q''\<in>{t. [Event e]\<^sub>E # t \<in> Q} \<and> add_Tick_refusal_trace \<sigma> \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q''"
        using 1 2 3 4 5 6 case_assms2(1) ind_hyp by blast
      then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Event e]\<^sub>E # add_Tick_refusal_trace \<sigma> \<in> x"
        using case_assms2 apply (rule_tac x="[Event e]\<^sub>E # p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event e]\<^sub>E # q''" in exI, auto)
        by (rule_tac x="[Event e]\<^sub>E # p''" in bexI, auto, rule_tac x="[Event e]\<^sub>E # q''" in bexI, auto)
    next
      fix p'
      assume case_assms2: "\<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "p = [Event e]\<^sub>E # p'" "e \<notin> A"
      have 1: "p' \<in> {t. [Event e]\<^sub>E # t \<in> P}"
        using case_assms(2) case_assms2(2) by blast
      have 2: "TT1 {t. [Event e]\<^sub>E # t \<in> P}"
        by (simp add: TT1_init_event case_assms(4))
      have 3: "TT4 {t. [Event e]\<^sub>E # t \<in> P}"
        by (simp add: TT4_init_event case_assms(6))
      obtain p'' q' where "p''\<in>{t. [Event e]\<^sub>E # t \<in> P} \<and> q' \<in> Q \<and> add_Tick_refusal_trace \<sigma> \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'"
        using 1 2 3 case_assms case_assms2(1) ind_hyp by blast
      then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Event e]\<^sub>E # add_Tick_refusal_trace \<sigma> \<in> x"
        using case_assms2 by (rule_tac x="[Event e]\<^sub>E # p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'" in exI, auto, cases q' rule:ttWF.cases, auto)
    next
      fix q'
      assume case_assms2: "\<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'" "q = [Event e]\<^sub>E # q'" "e \<notin> A"
      have 1: "q' \<in> {t. [Event e]\<^sub>E # t \<in> Q}"
        using case_assms case_assms2 by blast
      have 2: "TT1 {t. [Event e]\<^sub>E # t \<in> Q}"
        by (simp add: TT1_init_event case_assms(5))
      have 3: "TT4 {t. [Event e]\<^sub>E # t \<in> Q}"
        by (simp add: TT4_init_event case_assms(7))
      obtain p' q'' where "q''\<in>{t. [Event e]\<^sub>E # t \<in> Q} \<and> p' \<in> P \<and> add_Tick_refusal_trace \<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q''"
        using 1 2 3 case_assms case_assms2(1) ind_hyp by blast
      then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Event e]\<^sub>E # add_Tick_refusal_trace \<sigma> \<in> x"
        using case_assms2 by (rule_tac x=" p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event e]\<^sub>E # q''" in exI, auto, cases p' rule:ttWF.cases, auto)
    qed
  next
    fix X \<sigma> p q P Q
    assume ind_hyp: "\<And>p q P Q. TT1 P \<Longrightarrow> TT1 Q \<Longrightarrow> TT4 P \<Longrightarrow> TT4 Q \<Longrightarrow> \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> p \<in> P \<Longrightarrow> q \<in> Q \<Longrightarrow>
      \<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> add_Tick_refusal_trace \<sigma> \<in> x"
    assume case_assms: "TT1 P" "TT1 Q" "TT4 P" "TT4 Q" "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "p \<in> P" "q \<in> Q"
    then have "(\<exists> Y Z p' q'. p = [Y]\<^sub>R # [Tock]\<^sub>E # p' \<and> q = [Z]\<^sub>R # [Tock]\<^sub>E # q' \<and> X \<subseteq> Y \<union> Z \<and> {e \<in> Y. e \<notin> Event ` A \<union> {Tock, Tick}} = {e \<in> Z. e \<notin> Event ` A \<union> {Tock, Tick}} \<and> \<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')
      \<or> (\<exists> Z q'. p = [[Tick]\<^sub>E] \<and> q = [Z]\<^sub>R # [Tock]\<^sub>E # q' \<and> [[X]\<^sub>R] \<in> ([[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Z]\<^sub>R]) \<and> \<sigma> \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')
      \<or> (\<exists> Y p'. p = [Y]\<^sub>R # [Tock]\<^sub>E # p' \<and> q = [[Tick]\<^sub>E] \<and> [[X]\<^sub>R] \<in> ([[Y]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]) \<and> \<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E])"
      by (cases "(p,q)" rule:ttWF2.cases, simp_all)
    then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [insert Tick X]\<^sub>R # [Tock]\<^sub>E # add_Tick_refusal_trace \<sigma> \<in> x"
    proof (safe)
      fix Y Z p' q'
      assume case_assms2: "p = [Y]\<^sub>R # [Tock]\<^sub>E # p'" "q = [Z]\<^sub>R # [Tock]\<^sub>E # q'" "\<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'" "X \<subseteq> Y \<union> Z"
        "{e \<in> Y. e \<notin> Event ` A \<union> {Tock, Tick}} = {e \<in> Z. e \<notin> Event ` A \<union> {Tock, Tick}}"
      have 1: "p' \<in> {t. [Y]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
        using case_assms(6) case_assms2(1) by auto
      have 2: "TT1 {t. [Y]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
        by (simp add: TT1_init_tock case_assms(1))
      have 3: "TT4 {t. [Y]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
        by (simp add: TT4_TT1_init_tock case_assms(1) case_assms(3))
      have 4: "q' \<in> {t. [Z]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}"
        using case_assms(7) case_assms2(2) by auto
      have 5: "TT1 {t. [Z]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}"
        by (simp add: TT1_init_tock case_assms(2))
      have 6: "TT4 {t. [Z]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}"
        by (simp add: TT4_TT1_init_tock case_assms(2) case_assms(4))
      obtain  q'' p'' where "p'' \<in> {t. [Y]\<^sub>R # [Tock]\<^sub>E # t \<in> P} \<and> q'' \<in> {t. [Z]\<^sub>R # [Tock]\<^sub>E # t \<in> Q} \<and> add_Tick_refusal_trace \<sigma> \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q''"
        using "1" "2" "3" "4" "5" "6" case_assms2(3) ind_hyp by blast
      then have "p'' \<in> {t. [Y \<union> {Tick}]\<^sub>R # [Tock]\<^sub>E # t \<in> P} \<and> q'' \<in> {t. [Z \<union> {Tick}]\<^sub>R # [Tock]\<^sub>E # t \<in> Q} \<and> add_Tick_refusal_trace \<sigma> \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q''"
        using TT4_TT1_add_Tick_ref_Tock case_assms case_assms by auto
      then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [insert Tick X]\<^sub>R # [Tock]\<^sub>E # add_Tick_refusal_trace \<sigma> \<in> x"
        using case_assms case_assms2 apply (rule_tac x="[Y \<union> {Tick}]\<^sub>R # [Tock]\<^sub>E # p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Z \<union> {Tick}]\<^sub>R # [Tock]\<^sub>E # q''" in exI, safe, simp_all)
        by (rule_tac x="[Y \<union> {Tick}]\<^sub>R # [Tock]\<^sub>E # p''" in bexI, rule_tac x="[Z \<union> {Tick}]\<^sub>R # [Tock]\<^sub>E # q''" in bexI, simp_all, safe, blast+)
    next
      fix Z q'
      assume case_assms2: "p = [[Tick]\<^sub>E]" "q = [Z]\<^sub>R # [Tock]\<^sub>E # q'" "[[X]\<^sub>R] \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Z]\<^sub>R]" "\<sigma> \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'"
      have 1: "q' \<in> {t. [Z]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}"
        using case_assms(7) case_assms2(2) by auto
      have 2: "TT1 {t. [Z]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}"
        by (simp add: TT1_init_tock case_assms(2))
      have 3: "TT4 {t. [Z]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}"
        by (simp add: TT4_TT1_init_tock case_assms(2) case_assms(4))
      have 4: "TT1 {[], [[Tick]\<^sub>E]}"
        using TT_Skip unfolding TT_defs SkipTT_def by simp
      have 5: "TT4 {[], [[Tick]\<^sub>E]}"
        using TT4_Skip unfolding TT4_def SkipTT_def by simp
      have 6: "p \<in> {[], [[Tick]\<^sub>E]}"
        by (simp add: case_assms2(1))
      obtain p'' q'' where "p'' \<in> {[], [[Tick]\<^sub>E]} \<and> q'' \<in> {t. [Z]\<^sub>R # [Tock]\<^sub>E # t \<in> Q} \<and> add_Tick_refusal_trace \<sigma> \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q''"
        using 1 2 3 4 5 6 case_assms2 ind_hyp[where P="{[], [[Tick]\<^sub>E]}", where Q="{t. [Z]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}", where p=p, where q=q'] by auto
      then obtain q''' where "add_Tick_refusal_trace \<sigma> \<in> ([[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q''') \<and> q''' \<in> {t. [Z]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}"
        by (auto, smt "2" TT1_def mem_Collect_eq merge_traces_comm merge_traces_empty_merge_traces_tick)
      then have "add_Tick_refusal_trace \<sigma> \<in> ([[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q''') \<and> q''' \<in> {t. [Z \<union> {Tick}]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}"
        using TT4_TT1_add_Tick_ref_Tock case_assms(2) case_assms(4) by blast
      then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [insert Tick X]\<^sub>R # [Tock]\<^sub>E # add_Tick_refusal_trace \<sigma> \<in> x"
        using case_assms case_assms2 apply (rule_tac x="[[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [insert Tick Z]\<^sub>R # [Tock]\<^sub>E # q'''" in exI, safe)
        by (rule_tac x="[[Tick]\<^sub>E]" in bexI, rule_tac x="[insert Tick Z]\<^sub>R # [Tock]\<^sub>E # q'''" in bexI, auto)
    next
      fix Y p'
      assume case_assms2: "p = [Y]\<^sub>R # [Tock]\<^sub>E # p'" "q = [[Tick]\<^sub>E]" "[[X]\<^sub>R] \<in> [[Y]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" "\<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
      have 1: "p' \<in> {t. [Y]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
        using case_assms(6) case_assms2(1) by auto
      have 2: "TT1 {t. [Y]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
        by (simp add: TT1_init_tock case_assms(1))
      have 3: "TT4 {t. [Y]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
        by (simp add: TT4_TT1_init_tock case_assms(1) case_assms(3))
      have 4: "TT1 {[], [[Tick]\<^sub>E]}"
        using TT_Skip unfolding TT_defs SkipTT_def by simp
      have 5: "TT4 {[], [[Tick]\<^sub>E]}"
        using TT4_Skip unfolding TT4_def SkipTT_def by simp
      have 6: "q \<in> {[], [[Tick]\<^sub>E]}"
        by (simp add: case_assms2(2))
      obtain p'' q'' where "q'' \<in> {[], [[Tick]\<^sub>E]} \<and> p'' \<in> {t. [Y]\<^sub>R # [Tock]\<^sub>E # t \<in> P} \<and> add_Tick_refusal_trace \<sigma> \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q''"
        using 1 2 3 4 5 6 case_assms2 ind_hyp[where Q="{[], [[Tick]\<^sub>E]}", where P="{t. [Y]\<^sub>R # [Tock]\<^sub>E # t \<in> P}", where p=p', where q=q] by auto
      then obtain p''' where "add_Tick_refusal_trace \<sigma> \<in> (p''' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]) \<and> p''' \<in> {t. [Y]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
        by (auto, smt "2" TT1_def mem_Collect_eq merge_traces_comm merge_traces_empty_merge_traces_tick)
      then have "add_Tick_refusal_trace \<sigma> \<in> (p''' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]) \<and> p''' \<in> {t. [Y \<union> {Tick}]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
        using TT4_TT1_add_Tick_ref_Tock case_assms(1) case_assms(3) by blast
      then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [insert Tick X]\<^sub>R # [Tock]\<^sub>E # add_Tick_refusal_trace \<sigma> \<in> x"
        using case_assms case_assms2 apply (rule_tac x="[insert Tick Y]\<^sub>R # [Tock]\<^sub>E # p''' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" in exI, safe)
        by (rule_tac x="[insert Tick Y]\<^sub>R # [Tock]\<^sub>E # p'''" in bexI, rule_tac x="[[Tick]\<^sub>E]" in bexI, auto)
    qed
  next
    fix va p q P Q
    assume "[Tock]\<^sub>E # va \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Tock]\<^sub>E # add_Tick_refusal_trace va \<in> x"
      by (cases "(p,q)" rule:ttWF2.cases, auto)
  next
    fix va p q P Q
    assume "[Tock]\<^sub>E # va \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Tock]\<^sub>E # add_Tick_refusal_trace va \<in> x"
      by (cases "(p,q)" rule:ttWF2.cases, auto)
  next
    fix va p q P Q
    assume "[Tock]\<^sub>E # va \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Tock]\<^sub>E # add_Tick_refusal_trace va \<in> x"
      by (cases "(p,q)" rule:ttWF2.cases, auto)
  next
    fix v vc p q P Q
    assume "[Tick]\<^sub>E # v # vc \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Tick]\<^sub>E # add_Tick_refusal_trace (v # vc) \<in> x"
      by (cases "(p,q)" rule:ttWF2.cases, auto)
  next
    fix v vc p q P Q
    assume "[Tick]\<^sub>E # v # vc \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [Tick]\<^sub>E # add_Tick_refusal_trace (v # vc) \<in> x"
      by (cases "(p,q)" rule:ttWF2.cases, auto)
  next
    fix va vd vc p q P Q
    assume "[va]\<^sub>R # [Event vd]\<^sub>E # vc \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [insert Tick va]\<^sub>R # [Event vd]\<^sub>E # add_Tick_refusal_trace vc \<in> x"
      by (cases "(p,q)" rule:ttWF2.cases, auto)
  next
    fix va vc p q P Q
    assume "[va]\<^sub>R # [Tick]\<^sub>E # vc \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [insert Tick va]\<^sub>R # [Tick]\<^sub>E # add_Tick_refusal_trace vc \<in> x"
      by (cases "(p,q)" rule:ttWF2.cases, auto)
  next
    fix va v vc p q P Q
    assume "[va]\<^sub>R # [v]\<^sub>R # vc \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    then show "\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> [insert Tick va]\<^sub>R # [insert Tick v]\<^sub>R # add_Tick_refusal_trace vc \<in> x"
      by (cases "(p,q)" rule:ttWF2.cases, auto)
  qed
qed

lemma TT_ParComp:
  assumes "TT P" "TT Q"
  shows "TT (P \<lbrakk>A\<rbrakk>\<^sub>C Q)"
  using assms unfolding TT_def apply (safe)
  using ParCompTT_wf apply blast
  using TT0_ParComp unfolding TT_def apply blast
  using TT1_ParComp unfolding TT_def apply blast
  using TT2w_ParComp unfolding TT_def apply blast
  using TT3_ParComp unfolding TT_def apply blast
  done

function merge_traces2 :: "'e ttobs list \<Rightarrow> 'e set \<Rightarrow> 'e ttobs list \<Rightarrow> 'e ttobs list set" (infixl "\<lbrakk>_\<rbrakk>\<^sup>T\<^sub>2" 55) where
  "merge_traces2 [] Z [] = {[]}" | 
  "merge_traces2 [] Z [[Y]\<^sub>R] = {[]}" | (* if one side lacks a refusal, the composition lacks a refusal *) 
  "merge_traces2 [] Z [[Tick]\<^sub>E] = {[]}" | (* both must terminate together *)
  "merge_traces2 [] Z ([Event f]\<^sub>E # \<sigma>) = {t. f \<notin> Z \<and> (\<exists> s. s \<in> merge_traces2 [] Z \<sigma> \<and> t = [Event f]\<^sub>E # s)}" | (* the event from one side is performed *) 
  "merge_traces2 [] Z ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = {}" | (* Tock must always synchronise *)
  "merge_traces2 [[X]\<^sub>R] Z [] = {[]}" | (* if one side lacks a refusal, the composition lacks a refusal *) 
  "merge_traces2 [[X]\<^sub>R] Z [[Y]\<^sub>R] = {t. {e. e \<in> Y \<and> e \<notin> ((Event ` Z) \<union> {Tock, Tick})} = {e. e \<in> X \<and> e \<notin> ((Event ` Z) \<union> {Tock, Tick})} \<and> t = [[X \<union> Y]\<^sub>R]}" | (* intersect the refusals for non-synchronised events, union for synchronised events *) 
  "merge_traces2 [[X]\<^sub>R] Z [[Tick]\<^sub>E] = {t. \<exists>A\<subseteq>Z. t = [[X \<union> Event ` A]\<^sub>R]}" | (* treat Tick as refusing everything but Tock and Tick *) 
  "merge_traces2 [[X]\<^sub>R] Z ([Event f]\<^sub>E # \<sigma>) = {t. f \<notin> Z \<and> (\<exists> s. s \<in> merge_traces2 [[X]\<^sub>R] Z \<sigma> \<and> t = [Event f]\<^sub>E # s)}" | (* the event from one side is performed *)  
  "merge_traces2 [[X]\<^sub>R] Z ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = {}" | (* Tock must always synchronise*)  
  "merge_traces2 [[Tick]\<^sub>E] Z [] = {[]}" | (* both must terminate together *)
  "merge_traces2 [[Tick]\<^sub>E] Z [[Y]\<^sub>R] = {t. \<exists>A\<subseteq>Z. t = [[Y \<union> Event ` A]\<^sub>R]}" | (* treat Tick as refusing everything but Tock and Tick *)
  "merge_traces2 [[Tick]\<^sub>E] Z [[Tick]\<^sub>E] = {[[Tick]\<^sub>E]}" | (* both terminate together *)
  "merge_traces2 [[Tick]\<^sub>E] Z ([Event f]\<^sub>E # \<sigma>) = {t. f \<notin> Z \<and> (\<exists> s. s \<in> merge_traces2 [[Tick]\<^sub>E] Z \<sigma> \<and> t = [Event f]\<^sub>E # s)}" | (* the event from one side is performed *) 
  "merge_traces2 [[Tick]\<^sub>E] Z ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = {t. (\<exists> W s. [[W]\<^sub>R] \<in> merge_traces2 [[Tick]\<^sub>E] Z [[Y]\<^sub>R] \<and> s \<in> merge_traces2 [[Tick]\<^sub>E] Z \<sigma> \<and> t = [W]\<^sub>R # [Tock]\<^sub>E # s)}" | (* Tock must synchronize, but there are implicit tocks allowed after termination, the refusal set after Tick is everything *)
  "merge_traces2 ([Event e]\<^sub>E # \<sigma>) Z [] = {t. e \<notin> Z \<and> (\<exists> s. s \<in> merge_traces2 \<sigma> Z [] \<and> t = [Event e]\<^sub>E # s)}" | (* the event from one side is performed *)
  "merge_traces2 ([Event e]\<^sub>E # \<sigma>) Z [[Y]\<^sub>R] = {t. e \<notin> Z \<and> (\<exists> s. s \<in> merge_traces2 \<sigma> Z [[Y]\<^sub>R] \<and> t = [Event e]\<^sub>E # s)}" | (* *) 
  "merge_traces2 ([Event e]\<^sub>E # \<sigma>) Z [[Tick]\<^sub>E] = {t. e \<notin> Z \<and> (\<exists> s. s \<in> merge_traces2 \<sigma> Z [[Tick]\<^sub>E] \<and> t = [Event e]\<^sub>E # s)}" | (* *)  
  "merge_traces2 ([Event e]\<^sub>E # \<rho>) Z ([Event f]\<^sub>E # \<sigma>) = 
    {t. (e \<notin> Z \<and> f \<notin> Z \<and> ((\<exists> s. s \<in> merge_traces2 ([Event e]\<^sub>E # \<rho>) Z \<sigma> \<and> t = [Event f]\<^sub>E # s) \<or> (\<exists> s. s \<in> merge_traces2 \<rho> Z ([Event f]\<^sub>E # \<sigma>) \<and> t = [Event e]\<^sub>E # s)))
      \<or> (e \<in> Z \<and> f \<notin> Z \<and> (\<exists> s. s \<in> merge_traces2 ([Event e]\<^sub>E # \<rho>) Z \<sigma> \<and> t = [Event f]\<^sub>E # s))
      \<or> (e \<notin> Z \<and> f \<in> Z \<and> (\<exists> s. s \<in> merge_traces2 \<rho> Z ([Event f]\<^sub>E # \<sigma>) \<and> t = [Event e]\<^sub>E # s))
      \<or> (e \<in> Z \<and> f \<in> Z \<and> e = f \<and> (\<exists> s. s \<in> merge_traces2 \<rho> Z \<sigma> \<and> t = [Event e]\<^sub>E # s))}" | (* *) 
  "merge_traces2 ([Event e]\<^sub>E # \<rho>) Z ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = {t. e \<notin> Z \<and> (\<exists> s. s \<in> merge_traces2 \<rho> Z ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) \<and> t = [Event e]\<^sub>E # s)}" | (* *)  
  "merge_traces2 ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) Z [] = {}" | (* Tock must always synchronise*) 
  "merge_traces2 ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) Z [[Y]\<^sub>R] = {}" | (* Tock must always synchronise*)  
  "merge_traces2 ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) Z [[Tick]\<^sub>E] = {t. (\<exists> W s. [[W]\<^sub>R] \<in> merge_traces2 [[X]\<^sub>R] Z [[Tick]\<^sub>E] \<and> s \<in> merge_traces2 \<sigma> Z [[Tick]\<^sub>E] \<and> t = [W]\<^sub>R # [Tock]\<^sub>E # s)}" | (* Tock must synchronize, but there are implicit tocks allowed after termination, the refusal set after Tick is everything *)
  "merge_traces2 ([X]\<^sub>R # [Tock]\<^sub>E # \<rho>) Z ([Event f]\<^sub>E # \<sigma>) = {t. f \<notin> Z \<and> (\<exists> s. s \<in> merge_traces2 ([X]\<^sub>R # [Tock]\<^sub>E # \<rho>) Z \<sigma> \<and> t = [Event f]\<^sub>E # s)}" | (* *)  
  "merge_traces2 ([X]\<^sub>R # [Tock]\<^sub>E # \<rho>) Z ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = {t. (\<exists> W s. [[W]\<^sub>R] \<in> merge_traces2 [[X]\<^sub>R] Z [[Y]\<^sub>R] \<and> s \<in> merge_traces2 \<rho> Z \<sigma> \<and> t = [W]\<^sub>R # [Tock]\<^sub>E # s)}" | (* *) 
  (* non-well-formed traces produce empty sets *)
  "merge_traces2 ([X]\<^sub>R # [Tick]\<^sub>E # \<rho>) Z \<sigma> = {}" |
  "merge_traces2 ([X]\<^sub>R # [Event e]\<^sub>E # \<rho>) Z \<sigma> = {}" |
  "merge_traces2 ([X]\<^sub>R # [Y]\<^sub>R # \<rho>) Z \<sigma> = {}" |
  "merge_traces2 \<rho> Z ([X]\<^sub>R # [Tick]\<^sub>E # \<sigma>) = {}" |
  "merge_traces2 \<rho> Z ([X]\<^sub>R # [Event e]\<^sub>E # \<sigma>) = {}" |
  "merge_traces2 \<rho> Z ([X]\<^sub>R # [Y]\<^sub>R # \<sigma>) = {}" |
  "merge_traces2 ([Tick]\<^sub>E # x # \<rho>) Z \<sigma> = {}" |
  "merge_traces2 \<rho> Z ([Tick]\<^sub>E # y # \<sigma>) = {}" |
  "merge_traces2 ([Tock]\<^sub>E # \<rho>) Z \<sigma> = {}" |
  "merge_traces2 \<rho> Z ([Tock]\<^sub>E # \<sigma>) = {}"
  by (pat_completeness, simp_all)
termination by (lexicographic_order)

lemma merge_traces2_subset_merge_traces:
  "merge_traces2 x A y \<subseteq> merge_traces x A y"
  apply (induct x A y rule:merge_traces.induct, simp_all)
  apply (blast, blast, blast, blast, blast, blast, blast, blast)
  by (smt Collect_mono_iff subsetCE, blast, auto)

definition ParComp2TT :: "'e ttobs list set \<Rightarrow> 'e set \<Rightarrow> 'e ttobs list set \<Rightarrow> 'e ttobs list set" (infix "\<lbrakk>_\<rbrakk>\<^sub>2" 55) where
  "ParComp2TT P A Q = \<Union> {t. \<exists> p \<in> P. \<exists> q \<in> Q. t = merge_traces2 p A q}"

lemma ParComp2TT_subset_ParCompTT:
  "ParComp2TT P A Q \<subseteq> ParCompTT P A Q"
  unfolding ParComp2TT_def ParCompTT_def using merge_traces2_subset_merge_traces by blast

lemma merge_traces_subset_in_merge_traces2:
  "[[W]\<^sub>R] \<in> merge_traces [[X]\<^sub>R] A [[Y]\<^sub>R] \<and> x = [[W \<inter> X \<union> W \<inter> Y]\<^sub>R] \<and>
    {e \<in> W. e \<in> Y \<and> e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A} = {e \<in> W. e \<in> X \<and> e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A}
    \<Longrightarrow> \<exists> p' q'. p' \<lesssim>\<^sub>C [[X]\<^sub>R] \<and> q' \<lesssim>\<^sub>C [[Y]\<^sub>R] \<and> x \<in> merge_traces2 p' A q'"
  by (simp, rule_tac x="[[W \<inter> X]\<^sub>R]" in exI, simp, rule_tac x="[[W \<inter> Y]\<^sub>R]" in exI, simp)

lemma merge_traces2_empty2_prefix_subset_merge_traces2_Tick2:
  "\<And>t. t \<in> merge_traces2 x A [] \<Longrightarrow> \<exists> x'. x' \<lesssim>\<^sub>C x \<and> t \<in> merge_traces2 x' A [[Tick]\<^sub>E]"
proof (induct x rule:ttWF.induct, auto)
  show "\<exists>x'. x' \<lesssim>\<^sub>C [] \<and> [] \<in> x' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]"
    by (rule_tac x="[]" in exI, auto)
next
  fix X
  show "\<exists>x'. x' \<lesssim>\<^sub>C [[X]\<^sub>R] \<and> [] \<in> x' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]"
    by (rule_tac x="[]" in exI, auto)
next
  show "\<exists>x'. x' \<lesssim>\<^sub>C [[Tick]\<^sub>E] \<and> [] \<in> x' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]"
    by (rule_tac x="[]" in exI, auto)
next
  fix e \<sigma> s
  assume ind_hyp: "\<And>t. t \<in> \<sigma> \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [] \<Longrightarrow> \<exists>x'. x' \<lesssim>\<^sub>C \<sigma> \<and> t \<in> x' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]"
  assume case_assms: "e \<notin> A" "s \<in> \<sigma> \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 []"
  from ind_hyp and case_assms obtain x' where "x' \<lesssim>\<^sub>C \<sigma> \<and> s \<in> x' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]"
    by blast
  then show "\<exists>x'. x' \<lesssim>\<^sub>C [Event e]\<^sub>E # \<sigma> \<and> [Event e]\<^sub>E # s \<in> x' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]"
    by (rule_tac x="[Event e]\<^sub>E # x'" in exI, auto simp add: case_assms)
qed

lemma merge_traces2_empty1_prefix_subset_merge_traces2_Tick1:
  "\<And>t. t \<in> merge_traces2 [] A y \<Longrightarrow> \<exists> y'. y' \<lesssim>\<^sub>C y \<and> t \<in> merge_traces2 [[Tick]\<^sub>E] A y'"
proof (induct y rule:ttWF.induct, auto)
  show "\<exists>y'. y' \<lesssim>\<^sub>C [] \<and> [] \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 y'"
    by (rule_tac x="[]" in exI, auto)
next
  fix X
  show "\<exists>y'. y' \<lesssim>\<^sub>C [[X]\<^sub>R] \<and> [] \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 y'"
    by (rule_tac x="[]" in exI, auto)
next
  show "\<exists>y'. y' \<lesssim>\<^sub>C [[Tick]\<^sub>E] \<and> [] \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 y'"
    by (rule_tac x="[]" in exI, auto)
next
  fix e \<sigma> s
  assume ind_hyp: "\<And>t. t \<in> [] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 \<sigma> \<Longrightarrow> \<exists>y'. y' \<lesssim>\<^sub>C \<sigma> \<and> t \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 y'"
  assume case_assms: "e \<notin> A" "s \<in> [] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 \<sigma>"
  from ind_hyp and case_assms obtain y' where "y' \<lesssim>\<^sub>C \<sigma> \<and> s \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 y'"
    by blast
  then show "\<exists>y'. y' \<lesssim>\<^sub>C [Event e]\<^sub>E # \<sigma> \<and> [Event e]\<^sub>E # s \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 y'"
    by (rule_tac x="[Event e]\<^sub>E # y'" in exI, auto simp add: case_assms)
qed

lemma ParCompTT_subset_ParComp2TT:
  assumes TT1_P: "TT1 P" and TT1_Q: "TT1 Q"
  shows "ParCompTT P A Q \<subseteq> ParComp2TT P A Q"
  unfolding ParComp2TT_def ParCompTT_def
proof auto
  fix x p q
  have "\<And> p q P Q. TT1 P \<Longrightarrow> TT1 Q \<Longrightarrow> p \<in> P \<Longrightarrow> q \<in> Q \<Longrightarrow> x \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow>
    \<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> x \<in> xa"
  proof (induct x rule:ttWF.induct)
    fix P Q :: "'a ttobs list set"
    fix p q
    assume TT1_P: "TT1 P" and TT1_Q: "TT1 Q"
    assume p_in_P: "p \<in> P" and q_in_Q: "q \<in> Q"
    have TT0_P: "TT0 P"
      unfolding TT0_def using p_in_P by auto
    have TT0_Q: "TT0 Q"
      unfolding TT0_def using q_in_Q by auto
    show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> [] \<in> xa"
      apply (rule_tac x="{[]}" in exI, auto)
      using TT0_P TT0_Q TT0_TT1_empty TT1_P TT1_Q merge_traces2.simps(1) by blast
  next
    fix P Q :: "'a ttobs list set"
    fix X p q
    assume TT1_P: "TT1 P" and TT1_Q: "TT1 Q"
    assume p_in_P: "p \<in> P" and q_in_Q: "q \<in> Q"
    assume case_assm: "[[X]\<^sub>R] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    then have "(\<exists> Y Z. p = [[Y]\<^sub>R] \<and> q = [[Z]\<^sub>R])
        \<or> (\<exists> Z. p = [[Tick]\<^sub>E] \<and> q = [[Z]\<^sub>R])
        \<or> (\<exists> Y. p = [[Y]\<^sub>R] \<and> q = [[Tick]\<^sub>E])"
      by (cases "(p, q)" rule:ttWF2.cases, auto)
    then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> [[X]\<^sub>R] \<in> xa"
    proof auto
      fix Y Z
      assume p_q_assms: "p = [[Y]\<^sub>R]" "q = [[Z]\<^sub>R]"
      have Y_X_in_P: "[[Y \<inter> X]\<^sub>R] \<in> P"
        using TT1_P p_in_P p_q_assms unfolding TT1_def by force
      have Z_X_in_Q: "[[Z \<inter> X]\<^sub>R] \<in> Q"
        using TT1_Q q_in_Q p_q_assms unfolding TT1_def by force
      have Y_X_Z_X_merge:
        "{e \<in> Y \<inter> X. e \<notin> Event ` A \<union> {Tock, Tick}} = {e \<in> Z \<inter> X. e \<notin> Event ` A \<union> {Tock, Tick}}
          \<and> X \<subseteq> (Y \<inter> X) \<union> (Z \<inter> X)"
        using p_q_assms case_assm by auto
      from p_q_assms show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> [[X]\<^sub>R] \<in> xa"
        apply (rule_tac x="[[Y \<inter> X]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Z \<inter> X]\<^sub>R]" in exI, auto)
        apply (rule_tac x="[[Y \<inter> X]\<^sub>R]" in bexI, rule_tac x="[[Z \<inter> X]\<^sub>R]" in bexI)
        by (auto simp add: Y_X_in_P Z_X_in_Q, insert Y_X_Z_X_merge, blast+)
    next
      fix Z
      assume p_q_assms: "p = [[Tick]\<^sub>E]" "q = [[Z]\<^sub>R]"
      then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> [[X]\<^sub>R] \<in> xa"
        using p_in_P q_in_Q case_assm apply (rule_tac x="[[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Z]\<^sub>R]" in exI, auto)
        by (rule_tac x="[[Tick]\<^sub>E]" in bexI, rule_tac x="[[Z]\<^sub>R]" in bexI, auto)
    next
      fix Y
      assume p_q_assms: "p = [[Y]\<^sub>R]" "q = [[Tick]\<^sub>E]"
      then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> [[X]\<^sub>R] \<in> xa"
        using p_in_P q_in_Q case_assm apply (rule_tac x="[[Y]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]" in exI, auto)
        by (rule_tac x="[[Y]\<^sub>R]" in bexI, rule_tac x="[[Tick]\<^sub>E]" in bexI, auto)
    qed
  next
    fix P Q :: "'a ttobs list set"
    fix p q
    assume p_in_P: "p \<in> P" and q_in_Q: "q \<in> Q"
    assume "[[Tick]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> [[Tick]\<^sub>E] \<in> xa"
      using p_in_P q_in_Q apply (rule_tac x="[[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]" in exI, auto)
      apply (rule_tac x="[[Tick]\<^sub>E]" in bexI, rule_tac x="[[Tick]\<^sub>E]" in bexI, auto)
      by (cases "(p,q)" rule:ttWF2.cases, auto)+
  next
    fix P Q :: "'a ttobs list set"
    fix e \<sigma> p q
    assume TT1_P: "TT1 P" and TT1_Q: "TT1 Q"
    assume p_in_P: "p \<in> P" and q_in_Q: "q \<in> Q"
    assume ind_hyp: "\<And>p q P Q.
           TT1 P \<Longrightarrow>
           TT1 Q \<Longrightarrow> p \<in> P \<Longrightarrow> q \<in> Q \<Longrightarrow> \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> \<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> \<sigma> \<in> xa"
    assume case_assm: "[Event e]\<^sub>E # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    then have "(\<exists> p'. e \<notin> A \<and> p = [Event e]\<^sub>E # p' \<and> \<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q)
        \<or> (\<exists> q'. e \<notin> A \<and> q = [Event e]\<^sub>E # q' \<and> \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')
        \<or> (\<exists> p' q'. e \<in> A \<and> q = [Event e]\<^sub>E # q' \<and> p = [Event e]\<^sub>E # p' \<and> \<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
      by (cases "(p,q)" rule:ttWF2.cases, auto)
    then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> [Event e]\<^sub>E # \<sigma> \<in> xa"
    proof auto
      fix p'
      assume case_assms2: "e \<notin> A" "p = [Event e]\<^sub>E # p'" "\<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
      have "TT1 {t. [Event e]\<^sub>E # t \<in> P}"
        by (simp add: TT1_P TT1_init_event)
      then obtain p'' q'' where "p'' \<in> {t. [Event e]\<^sub>E # t \<in> P} \<and> q'' \<in> Q \<and> \<sigma> \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q''"
        using ind_hyp TT1_Q p_in_P q_in_Q case_assms2 by blast
      then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> [Event e]\<^sub>E # \<sigma> \<in> xa"
        apply (rule_tac x="[Event e]\<^sub>E # p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q''" in exI, auto)
        by (cases q'' rule:ttWF.cases, auto simp add: case_assms2)
    next
      fix q'
      assume case_assms2: "e \<notin> A" "q = [Event e]\<^sub>E # q'" "\<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'"
      have "TT1 {t. [Event e]\<^sub>E # t \<in> Q}"
        by (simp add: TT1_Q TT1_init_event)
      then obtain p'' q'' where "p'' \<in> P \<and> q'' \<in> {t. [Event e]\<^sub>E # t \<in> Q} \<and> \<sigma> \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q''"
        using ind_hyp TT1_P p_in_P q_in_Q case_assms2 by blast
      then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> [Event e]\<^sub>E # \<sigma> \<in> xa"
        apply (rule_tac x="p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [Event e]\<^sub>E # q''" in exI, auto)
        by (cases p'' rule:ttWF.cases, auto simp add: case_assms2)
    next
      fix p' q'
      assume case_assms2: "e \<in> A" "q = [Event e]\<^sub>E # q'" "p = [Event e]\<^sub>E # p'" "\<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'"
      have "TT1 {t. [Event e]\<^sub>E # t \<in> P} \<and> TT1 {t. [Event e]\<^sub>E # t \<in> Q}"
        by (simp add: TT1_Q TT1_P TT1_init_event)
      then obtain p'' q'' where "p'' \<in> {t. [Event e]\<^sub>E # t \<in> P} \<and> q'' \<in> {t. [Event e]\<^sub>E # t \<in> Q} \<and> \<sigma> \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q''"
        using ind_hyp p_in_P q_in_Q case_assms2 by blast
      then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> [Event e]\<^sub>E # \<sigma> \<in> xa"
        apply (rule_tac x="[Event e]\<^sub>E # p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [Event e]\<^sub>E # q''" in exI, auto)
        apply (rule_tac x="[Event e]\<^sub>E # p''" in bexI, auto)
        by (rule_tac x="[Event e]\<^sub>E # q''" in bexI, auto simp add: case_assms2)
    qed
  next
    fix P Q :: "'a ttobs list set"
    fix X \<sigma> p q
    assume TT1_P: "TT1 P" and TT1_Q: "TT1 Q"
    assume p_in_P: "p \<in> P" and q_in_Q: "q \<in> Q"
    assume ind_hyp: "\<And>p q P Q.
           TT1 P \<Longrightarrow>
           TT1 Q \<Longrightarrow> p \<in> P \<Longrightarrow> q \<in> Q \<Longrightarrow> \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> \<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> \<sigma> \<in> xa"
    assume case_assm: "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    then have "(\<exists> Z p'. \<sigma> \<in> (p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p = [Z]\<^sub>R # [Tock]\<^sub>E # p' \<and> q = [[Tick]\<^sub>E])
        \<or> (\<exists> W q'. \<sigma> \<in> (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q') \<and> p = [[Tick]\<^sub>E] \<and> q = [W]\<^sub>R # [Tock]\<^sub>E # q')
        \<or> (\<exists> Z W p' q'. \<sigma> \<in> (p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q') \<and> p = [Z]\<^sub>R # [Tock]\<^sub>E # p' \<and> q = [W]\<^sub>R # [Tock]\<^sub>E # q')"
      by (cases "(p,q)" rule:ttWF2.cases, auto)
    then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> xa"
    proof auto
      fix Z p'
      assume case_assms2: "\<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]" "p = [Z]\<^sub>R # [Tock]\<^sub>E # p'" "q = [[Tick]\<^sub>E]"
      have TT1s: "TT1 {t. [Z]\<^sub>R # [Tock]\<^sub>E # t \<in> P} \<and> TT1 {[], [[Tick]\<^sub>E]}"
        apply (simp add: TT1_P TT1_init_tock)
        unfolding TT1_def apply auto by (case_tac \<rho> rule:ttWF.cases, auto)+
      then have "\<exists>xa. (\<exists>p\<in>{t. [Z]\<^sub>R # [Tock]\<^sub>E # t \<in> P}. \<exists>q\<in>{[], [[Tick]\<^sub>E]}. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> \<sigma> \<in> xa"
        using ind_hyp TT1_Q p_in_P q_in_Q case_assm case_assms2 by blast
      then obtain p'' q'' where "p'' \<in> {t. [Z]\<^sub>R # [Tock]\<^sub>E # t \<in> P} \<and> q'' \<in> {[], [[Tick]\<^sub>E]} \<and> \<sigma> \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q''"
        by auto
      then obtain p''' where "p''' \<in> {t. [Z]\<^sub>R # [Tock]\<^sub>E # t \<in> P} \<and> \<sigma> \<in> p''' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]"
        by (metis TT1_def TT1s insert_iff merge_traces2_empty2_prefix_subset_merge_traces2_Tick2 singletonD)
      then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> xa"
        apply (rule_tac x="[Z]\<^sub>R # [Tock]\<^sub>E # p''' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]" in exI, simp_all, safe)
        apply (rule_tac x="[Z]\<^sub>R # [Tock]\<^sub>E # p'''" in bexI, rule_tac x="[[Tick]\<^sub>E]" in bexI, simp_all)
        using case_assm case_assms2 q_in_Q by auto
    next
      fix W q'
      assume case_assms2: "\<sigma> \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'" "q = [W]\<^sub>R # [Tock]\<^sub>E # q'" "p = [[Tick]\<^sub>E]"
      have TT1s: "TT1 {t. [W]\<^sub>R # [Tock]\<^sub>E # t \<in> Q} \<and> TT1 {[], [[Tick]\<^sub>E]}"
        apply (simp add: TT1_Q TT1_init_tock)
        unfolding TT1_def apply auto by (case_tac \<rho> rule:ttWF.cases, auto)+
      then have "\<exists>xa. (\<exists>p\<in>{[], [[Tick]\<^sub>E]}. \<exists>q\<in>{t. [W]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> \<sigma> \<in> xa"
        using ind_hyp p_in_P q_in_Q case_assms2 by blast
      then obtain p'' q'' where "q'' \<in> {t. [W]\<^sub>R # [Tock]\<^sub>E # t \<in> Q} \<and> p'' \<in> {[], [[Tick]\<^sub>E]} \<and> \<sigma> \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q''"
        by auto
      then obtain q''' where "q''' \<in> {t. [W]\<^sub>R # [Tock]\<^sub>E # t \<in> Q} \<and> \<sigma> \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q'''"
        by (metis TT1_def TT1s insert_iff merge_traces2_empty1_prefix_subset_merge_traces2_Tick1 singletonD)
      then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> xa"
        apply (rule_tac x="[[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [W]\<^sub>R # [Tock]\<^sub>E # q'''" in exI, simp_all, safe)
        apply (rule_tac x="[[Tick]\<^sub>E]" in bexI, rule_tac x="[W]\<^sub>R # [Tock]\<^sub>E # q'''" in bexI, simp_all)
        using case_assm case_assms2 p_in_P by auto
    next
      fix Z W p' q'
      assume case_assms2: "\<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'" "p = [Z]\<^sub>R # [Tock]\<^sub>E # p'" "q = [W]\<^sub>R # [Tock]\<^sub>E # q'"
      have sets_partial_eq: "{e \<in> Z. e \<notin> Event ` A \<union> {Tock, Tick}} = {e \<in> W. e \<notin> Event ` A \<union> {Tock, Tick}}"
        using case_assm case_assms2 by auto
      have X_subset_Z_W: "X \<subseteq> Z \<union> W"
        using case_assm case_assms2 by auto
      have "TT1 {t. [Z]\<^sub>R # [Tock]\<^sub>E # t \<in> P} \<and> TT1 {t. [W]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}"
        by (simp add: TT1_P TT1_Q TT1_init_tock)
      then obtain p'' q'' where "p'' \<in> {t. [Z]\<^sub>R # [Tock]\<^sub>E # t \<in> P} \<and> q'' \<in> {t. [W]\<^sub>R # [Tock]\<^sub>E # t \<in> Q} \<and> \<sigma> \<in> p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q''"
        using ind_hyp p_in_P q_in_Q case_assms2 by blast
      then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> xa"
        apply (rule_tac x="[X \<inter> Z]\<^sub>R # [Tock]\<^sub>E # p'' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [X \<inter> W]\<^sub>R # [Tock]\<^sub>E # q''" in exI, simp_all, safe)
        apply (rule_tac x="[X \<inter> Z]\<^sub>R # [Tock]\<^sub>E # p''" in bexI, rule_tac x="[X \<inter> W]\<^sub>R # [Tock]\<^sub>E # q''" in bexI)
        apply (auto simp add: case_assm case_assms2)
        using tt_prefix_subset_refl TT1_Q unfolding TT1_def
        apply (erule_tac x="[X \<inter> W]\<^sub>R # [Tock]\<^sub>E # q''" in allE, erule_tac x="[W]\<^sub>R # [Tock]\<^sub>E # q''" in allE, force)
        using tt_prefix_subset_refl TT1_P unfolding TT1_def
        apply (erule_tac x="[X \<inter> Z]\<^sub>R # [Tock]\<^sub>E # p''" in allE, erule_tac x="[Z]\<^sub>R # [Tock]\<^sub>E # p''" in allE, force)
        using sets_partial_eq X_subset_Z_W by (blast, blast, blast)
    qed
  next
    fix va p q P Q
    assume "[Tock]\<^sub>E # va \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> [Tock]\<^sub>E # va \<in> xa"
      by (cases "(p,q)" rule:ttWF2.cases, auto)
  next
    fix v vc p q P Q
    assume "[Tock]\<^sub>E # v # vc \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> [Tock]\<^sub>E # v # vc \<in> xa"
      by (cases "(p,q)" rule:ttWF2.cases, auto)
  next
    fix v vc p q P Q
    assume "[Tick]\<^sub>E # v # vc \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> [Tick]\<^sub>E # v # vc \<in> xa"
      by (cases "(p,q)" rule:ttWF2.cases, auto)
  next
    fix vb vc p q P Q
    assume "[Tock]\<^sub>E # vb # vc \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> [Tock]\<^sub>E # vb # vc \<in> xa"
      by (cases "(p,q)" rule:ttWF2.cases, auto)
  next
    fix vb vc p q P Q
    assume "[Tick]\<^sub>E # vb # vc \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> [Tick]\<^sub>E # vb # vc \<in> xa"
      by (cases "(p,q)" rule:ttWF2.cases, auto)
  next
    fix va vd vc p q P Q
    assume "[va]\<^sub>R # [Event vd]\<^sub>E # vc \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> [va]\<^sub>R # [Event vd]\<^sub>E # vc \<in> xa"
      by (cases "(p,q)" rule:ttWF2.cases, auto)
  next
    fix va vc p q P Q
    assume "[va]\<^sub>R # [Tick]\<^sub>E # vc \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> [va]\<^sub>R # [Tick]\<^sub>E # vc \<in> xa"
      by (cases "(p,q)" rule:ttWF2.cases, auto)
  next
    fix va v vc p q P Q
    assume "[va]\<^sub>R # [v]\<^sub>R # vc \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> [va]\<^sub>R # [v]\<^sub>R # vc \<in> xa"
      by (cases "(p,q)" rule:ttWF2.cases, auto)
  qed
  then show "x \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> p \<in> P \<Longrightarrow> q \<in> Q \<Longrightarrow> \<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>Q. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> x \<in> xa"
    using assms by auto
qed

lemma ParCompTT_eq_ParComp2TT:
  assumes "TT1 P" "TT1 Q"
  shows "(P \<lbrakk>A\<rbrakk>\<^sub>C Q) = (P \<lbrakk>A\<rbrakk>\<^sub>2 Q)"
  using assms ParCompTT_subset_ParComp2TT ParComp2TT_subset_ParCompTT by blast

lemma merge_traces2_comm:
  "merge_traces2 x A y = merge_traces2 y A x"
  by (induct x A y rule:merge_traces2.induct, simp_all, blast+)

lemma ParComp2_comm:
  "(P \<lbrakk>A\<rbrakk>\<^sub>2 Q) = (Q \<lbrakk>A\<rbrakk>\<^sub>2 P)"
  unfolding ParComp2TT_def using merge_traces2_comm by (auto, blast+)

lemma ParComp2_IntChoice_dist:
  "(P \<lbrakk>A\<rbrakk>\<^sub>2 (Q \<sqinter>\<^sub>C R)) = (P \<lbrakk>A\<rbrakk>\<^sub>2 Q) \<sqinter>\<^sub>C (P \<lbrakk>A\<rbrakk>\<^sub>2 R)"
  unfolding ParComp2TT_def IntChoiceTT_def
  apply (auto, erule_tac x="p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q" in allE, simp)
  by (erule_tac x="p" in ballE, erule_tac x="q" in ballE, simp_all)

lemma merge_traces2_prefix_subset:
  "\<And> p q. t \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q \<Longrightarrow> t' \<lesssim>\<^sub>C t \<Longrightarrow> \<exists> p' q'. p' \<lesssim>\<^sub>C p \<and> q' \<lesssim>\<^sub>C q \<and> t' \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q'"
proof (induct t' t rule:ttWF2.induct, simp_all)
  fix p q
  show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
    by (rule_tac x="[]" in exI, simp, rule_tac x="[]" in exI, simp)
next
  fix p q
  show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
    by (rule_tac x="[]" in exI, simp, rule_tac x="[]" in exI, simp)
next
  fix p q
  show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
    by (rule_tac x="[]" in exI, simp, rule_tac x="[]" in exI, simp)
next
  fix p q
  show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
    by (rule_tac x="[]" in exI, simp, rule_tac x="[]" in exI, simp)
next
  fix p q
  show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
    by (rule_tac x="[]" in exI, simp, rule_tac x="[]" in exI, simp)
next
  fix X Y p q
  assume case_assms: "[[Y]\<^sub>R] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q" "X \<subseteq> Y"
  then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [[X]\<^sub>R] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
  proof (cases "(p,q)" rule:ttWF2.cases, simp_all, safe)
    fix Xa Ya
    assume case_assms2: "[[Xa \<union> Ya]\<^sub>R] \<in> [[Xa]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Ya]\<^sub>R]" "X \<subseteq> Xa \<union> Ya"
      "{e \<in> Ya. e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A} = {e \<in> Xa. e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A}"
    then show "\<exists>p'. p' \<lesssim>\<^sub>C [[Xa]\<^sub>R] \<and> (\<exists>q'. q' \<lesssim>\<^sub>C [[Ya]\<^sub>R] \<and> [[X]\<^sub>R] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
      by (rule_tac x="[[Xa \<inter> X]\<^sub>R]" in exI, simp, rule_tac x="[[Ya \<inter> X]\<^sub>R]" in exI, auto)
  next
    fix Xa Aa
    assume case_assms2: "X \<subseteq> Xa \<union> Event ` Aa" "[[Xa \<union> Event ` Aa]\<^sub>R] \<in> [[Xa]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]" "Aa \<subseteq> A"
    then show "\<exists>p'. p' \<lesssim>\<^sub>C [[Xa]\<^sub>R] \<and> (\<exists>q'. q' \<lesssim>\<^sub>C [[Tick]\<^sub>E] \<and> [[X]\<^sub>R] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
      apply (rule_tac x="[[X \<inter> Xa]\<^sub>R]" in exI, simp, rule_tac x="[[Tick]\<^sub>E]" in exI, simp)
      by (smt Int_subset_iff inf.order_iff inf_right_idem inf_sup_distrib1 subset_image_iff)
  next
    fix Ya Aa
    assume case_assms2: "X \<subseteq> Ya \<union> Event ` Aa" "[[Ya \<union> Event ` Aa]\<^sub>R] \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Ya]\<^sub>R]" "Aa \<subseteq> A"
    then show "\<exists>p'. p' \<lesssim>\<^sub>C [[Tick]\<^sub>E] \<and> (\<exists>q'. q' \<lesssim>\<^sub>C [[Ya]\<^sub>R] \<and> [[X]\<^sub>R] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
      apply (rule_tac x="[[Tick]\<^sub>E]" in exI, simp, rule_tac x="[[X \<inter> Ya]\<^sub>R]" in exI, simp)
      by (smt Int_subset_iff inf.order_iff inf_right_idem inf_sup_distrib1 subset_image_iff)
  qed
next
  fix X Y \<sigma> p q
  assume case_assms: "[Y]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q" "X \<subseteq> Y"
  then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [[X]\<^sub>R] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
  proof (cases "(p,q)" rule:ttWF2.cases, simp_all, safe)
    fix Ya \<sigma>' Aa
    assume case_assms2: "X \<subseteq> Ya \<union> Event ` Aa" "\<sigma> \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 \<sigma>'" "Aa \<subseteq> A"
      "[Ya \<union> Event ` Aa]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [Ya]\<^sub>R # [Tock]\<^sub>E # \<sigma>'"
    then show "\<exists>p'. p' \<lesssim>\<^sub>C [[Tick]\<^sub>E] \<and> (\<exists>q'. q' \<lesssim>\<^sub>C [Ya]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<and> [[X]\<^sub>R] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
      apply (rule_tac x="[[Tick]\<^sub>E]" in exI, simp, rule_tac x="[[X \<inter> Ya]\<^sub>R]" in exI, simp)
      by (smt Int_subset_iff inf.order_iff inf_right_idem inf_sup_distrib1 subset_image_iff)
  next
    fix Xa \<sigma>' Aa
    assume case_assms2: "X \<subseteq> Xa \<union> Event ` Aa" "\<sigma> \<in> \<sigma>' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]" "Aa \<subseteq> A"
      "[Xa \<union> Event ` Aa]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> [Xa]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]"
    then show "\<exists>p'. p' \<lesssim>\<^sub>C [Xa]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<and> (\<exists>q'. q' \<lesssim>\<^sub>C [[Tick]\<^sub>E] \<and> [[X]\<^sub>R] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
      apply (rule_tac x="[[X \<inter> Xa]\<^sub>R]" in exI, simp, rule_tac x="[[Tick]\<^sub>E]" in exI, simp)
      by (smt Int_subset_iff inf.order_iff inf_right_idem inf_sup_distrib1 subset_image_iff)
  next
    fix Xa \<rho> Ya \<sigma>'
    assume case_assms2: "X \<subseteq> Xa \<union> Ya" "\<sigma> \<in> \<rho> \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 \<sigma>'"
       "[Xa \<union> Ya]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> [Xa]\<^sub>R # [Tock]\<^sub>E # \<rho> \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [Ya]\<^sub>R # [Tock]\<^sub>E # \<sigma>'"
       "{e \<in> Ya. e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A} = {e \<in> Xa. e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A}"
    then show "\<exists>p'. p' \<lesssim>\<^sub>C [Xa]\<^sub>R # [Tock]\<^sub>E # \<rho> \<and> (\<exists>q'. q' \<lesssim>\<^sub>C [Ya]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<and> [[X]\<^sub>R] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
      by (rule_tac x="[[X \<inter> Xa]\<^sub>R]" in exI, simp, rule_tac x="[[X \<inter> Ya]\<^sub>R]" in exI, simp, blast)
  qed
next
  fix p q
  assume case_assms: "[[Tick]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q"
  then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [[Tick]\<^sub>E] \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
    apply (cases "(p,q)" rule:ttWF2.cases, auto)
    by (rule_tac x="[[Tick]\<^sub>E]" in exI, simp, rule_tac x="[[Tick]\<^sub>E]" in exI, simp)
next
  fix e \<rho> f \<sigma> p q
  assume ind_hyp: "\<And>p q. \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q \<Longrightarrow> \<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
  assume case_assms: "[Event f]\<^sub>E # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q" "e = f \<and> \<rho> \<lesssim>\<^sub>C \<sigma>"
  then have p_q_cases: "(\<exists> p' q'. f \<in> A \<and> p = [Event f]\<^sub>E # p' \<and> q = [Event f]\<^sub>E # q')
                  \<or> (\<exists> p'. f \<notin> A \<and> p = [Event f]\<^sub>E # p' \<and> \<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)
                  \<or> (\<exists> q'. f \<notin> A \<and> q = [Event f]\<^sub>E # q' \<and> \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
    by (cases "(p,q)" rule:ttWF2.cases, auto)
  then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [Event f]\<^sub>E # \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
  proof auto
    fix p' q'
    assume case_assms2: "f \<in> A" "p = [Event f]\<^sub>E # p'" "q = [Event f]\<^sub>E # q'"
    then have "\<exists>p'a. p'a \<lesssim>\<^sub>C p' \<and> (\<exists>q'a. q'a \<lesssim>\<^sub>C q' \<and> \<rho> \<in> p'a \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q'a)"
      using case_assms ind_hyp[where p=p', where q=q'] by auto
    then show "\<exists>p'a. p'a \<lesssim>\<^sub>C [Event f]\<^sub>E # p' \<and> (\<exists>q'a. q'a \<lesssim>\<^sub>C [Event f]\<^sub>E # q' \<and> [Event f]\<^sub>E # \<rho> \<in> p'a \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q'a)"
      using case_assms case_assms2 apply auto
      by (rule_tac x="[Event f]\<^sub>E # p'a" in exI, simp, rule_tac x="[Event f]\<^sub>E # q'a" in exI, simp)
  next
    fix p'
    assume case_assms2: "f \<notin> A" "p = [Event f]\<^sub>E # p'" "\<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q"
    then have "\<exists>p'a. p'a \<lesssim>\<^sub>C p' \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> \<rho> \<in> p'a \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
      using case_assms ind_hyp[where p=p', where q=q] by auto
    then show "\<exists>p'a. p'a \<lesssim>\<^sub>C [Event f]\<^sub>E # p' \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [Event f]\<^sub>E # \<rho> \<in> p'a \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
      using case_assms case_assms2 apply auto
      by (rule_tac x="[Event f]\<^sub>E # p'a" in exI, simp, rule_tac x="q'" in exI, simp, case_tac q' rule:ttWF.cases, auto)
  next
    fix q'
    assume case_assms2: "f \<notin> A" "q = [Event f]\<^sub>E # q'" "\<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q'"
    then have "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'a. q'a \<lesssim>\<^sub>C q' \<and> \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q'a)"
      using case_assms ind_hyp[where p=p, where q=q'] by auto
    then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'a. q'a \<lesssim>\<^sub>C [Event f]\<^sub>E # q' \<and> [Event f]\<^sub>E # \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q'a)"
      using case_assms case_assms2 apply auto
      by (rule_tac x="p'" in exI, simp, rule_tac x="[Event f]\<^sub>E # q'a" in exI, simp, case_tac p' rule:ttWF.cases, auto)
  qed
next
  fix X \<rho> Y \<sigma> p q
  assume ind_hyp: "\<And>p q. \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q \<Longrightarrow> \<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
  assume case_assms: "[Y]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q" "X \<subseteq> Y \<and> \<rho> \<lesssim>\<^sub>C \<sigma>"
  then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
  proof (cases "(p,q)" rule:ttWF2.cases, simp_all, safe)
    fix Ya \<sigma>' Aa
    assume case_assms2: "[Ya \<union> Event ` Aa]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [Ya]\<^sub>R # [Tock]\<^sub>E # \<sigma>'"
      "\<sigma> \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 \<sigma>'" "X \<subseteq> Ya \<union> Event ` Aa" "\<rho> \<lesssim>\<^sub>C \<sigma>" "Aa \<subseteq> A"
    then have "\<exists>p'. p' \<lesssim>\<^sub>C [[Tick]\<^sub>E] \<and> (\<exists>q'. q' \<lesssim>\<^sub>C \<sigma>' \<and> \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
      using case_assms ind_hyp[where p="[[Tick]\<^sub>E]", where q="\<sigma>'"] by auto
    then have "\<exists>q'. q' \<lesssim>\<^sub>C \<sigma>' \<and> \<rho> \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q'"
      apply (auto, case_tac p' rule:ttWF.cases, auto)
      using merge_traces2_empty1_prefix_subset_merge_traces2_Tick1 tt_prefix_subset_trans by blast
    then show "\<exists>p'. p' \<lesssim>\<^sub>C [[Tick]\<^sub>E] \<and> (\<exists>q'. q' \<lesssim>\<^sub>C [Ya]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
      using case_assms case_assms2 apply auto
      apply (rule_tac x="[[Tick]\<^sub>E]" in exI, simp, rule_tac x="[Ya \<inter> X]\<^sub>R # [Tock]\<^sub>E # q'" in exI, simp)
      by (rule_tac x="{x. x \<in> Ab \<and> Event x \<in> X}" in exI, blast)
  next
    fix Xa \<sigma>' Aa
    assume case_assms2: "[Xa \<union> Event ` Aa]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> [Xa]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]"
      "\<sigma> \<in> \<sigma>' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]" "X \<subseteq> Xa \<union> Event ` Aa" "\<rho> \<lesssim>\<^sub>C \<sigma>" "Aa \<subseteq> A"
    then have "\<exists>p'. p' \<lesssim>\<^sub>C \<sigma>' \<and> (\<exists>q'. q' \<lesssim>\<^sub>C [[Tick]\<^sub>E] \<and> \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
      using case_assms ind_hyp[where q="[[Tick]\<^sub>E]", where p="\<sigma>'"] by auto
    then have "\<exists>p'. p' \<lesssim>\<^sub>C \<sigma>' \<and> \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]"
      apply (auto, case_tac q' rule:ttWF.cases, auto)
      using merge_traces2_empty2_prefix_subset_merge_traces2_Tick2 tt_prefix_subset_trans by blast
    then show "\<exists>p'. p' \<lesssim>\<^sub>C [Xa]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<and> (\<exists>q'. q' \<lesssim>\<^sub>C [[Tick]\<^sub>E] \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
      using case_assms case_assms2 apply auto
      apply (rule_tac x="[Xa \<inter> X]\<^sub>R # [Tock]\<^sub>E # p'" in exI, simp, rule_tac x="[[Tick]\<^sub>E]" in exI, simp)
      by (rule_tac x="{x. x \<in> Ab \<and> Event x \<in> X}" in exI, blast)
  next
    fix Xa \<rho>' Ya \<sigma>'
    assume case_assms2: "[Xa \<union> Ya]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> [Xa]\<^sub>R # [Tock]\<^sub>E # \<rho>' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [Ya]\<^sub>R # [Tock]\<^sub>E # \<sigma>'"
       "{e \<in> Ya. e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A} = {e \<in> Xa. e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A}"
       "X \<subseteq> Xa \<union> Ya" "\<rho> \<lesssim>\<^sub>C \<sigma>" "\<sigma> \<in> \<rho>' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 \<sigma>'"
    then have "\<exists>p'. p' \<lesssim>\<^sub>C \<rho>' \<and> (\<exists>q'. q' \<lesssim>\<^sub>C \<sigma>' \<and> \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
      using case_assms ind_hyp[where p=\<rho>', where q=\<sigma>'] by auto
    then show "\<exists>p'. p' \<lesssim>\<^sub>C [Xa]\<^sub>R # [Tock]\<^sub>E # \<rho>' \<and> (\<exists>q'. q' \<lesssim>\<^sub>C [Ya]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
      using case_assms2 apply safe
      by (rule_tac x="[Xa \<inter> X]\<^sub>R # [Tock]\<^sub>E # p'" in exI, simp, rule_tac x="[Ya \<inter> X]\<^sub>R # [Tock]\<^sub>E # q'" in exI, auto)
  qed
next
  fix X \<rho> \<sigma> p q
  assume "\<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q" "[X]\<^sub>R # [Tick]\<^sub>E # \<rho> \<lesssim>\<^sub>C \<sigma>"
  then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [X]\<^sub>R # [Tick]\<^sub>E # \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
    by (cases \<sigma> rule:ttWF.cases, auto, cases "(p,q)" rule:ttWF2.cases, auto)
next
  fix X e \<rho> \<sigma> p q
  assume "\<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q" "[X]\<^sub>R # [Event e]\<^sub>E # \<rho> \<lesssim>\<^sub>C \<sigma>"
  then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [X]\<^sub>R # [Event e]\<^sub>E # \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
    by (cases \<sigma> rule:ttWF.cases, auto, cases "(p,q)" rule:ttWF2.cases, auto)
next
  fix X Y \<rho> \<sigma> p q
  assume "\<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q" "[X]\<^sub>R # [Y]\<^sub>R # \<rho> \<lesssim>\<^sub>C \<sigma>"
  then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [X]\<^sub>R # [Y]\<^sub>R # \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
    by (cases \<sigma> rule:ttWF.cases, auto, cases "(p,q)" rule:ttWF2.cases, auto)
next
  fix \<rho> X \<sigma> p q
  assume "[X]\<^sub>R # [Tick]\<^sub>E # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q"
  then show "\<rho> \<lesssim>\<^sub>C [X]\<^sub>R # [Tick]\<^sub>E # \<sigma> \<Longrightarrow> \<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
    by (cases "(p,q)" rule:ttWF2.cases, auto)
next
  fix \<rho> X e \<sigma> p q
  assume "[X]\<^sub>R # [Event e]\<^sub>E # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q"
  then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
    by (cases "(p,q)" rule:ttWF2.cases, auto)
next
  fix \<rho> X Y \<sigma> p q
  assume "[X]\<^sub>R # [Y]\<^sub>R # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q"
  then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
    by (cases "(p,q)" rule:ttWF2.cases, auto)
next
  fix x \<rho> \<sigma> p q
  assume "\<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q" "[Tick]\<^sub>E # x # \<rho> \<lesssim>\<^sub>C \<sigma>"
  then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [Tick]\<^sub>E # x # \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
    by (cases \<sigma> rule:ttWF.cases, auto, (cases "(p,q)" rule:ttWF2.cases, auto)+)
next
  fix \<rho> y \<sigma> p q
  assume "[Tick]\<^sub>E # y # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q"
  then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
    by (cases "(p,q)" rule:ttWF2.cases, auto)
next
  fix \<rho> \<sigma> p q
  assume "\<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q" "[Tock]\<^sub>E # \<rho> \<lesssim>\<^sub>C \<sigma>"
  then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [Tock]\<^sub>E # \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
    by (cases \<sigma> rule:ttWF.cases, auto, (cases "(p,q)" rule:ttWF2.cases, auto)+)
next
  fix \<rho> \<sigma> p q
  assume "[Tock]\<^sub>E # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q"
  then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> \<rho> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
    by (cases "(p,q)" rule:ttWF2.cases, auto)
qed

lemma ParComp2_assoc_subset1: 
  assumes TT1_P: "TT1 P" and TT1_Q: "TT1 Q" and TT1_R: "TT1 R"
  shows "((P \<lbrakk>A\<rbrakk>\<^sub>2 Q) \<lbrakk>A\<rbrakk>\<^sub>2 R) \<subseteq> (P \<lbrakk>A\<rbrakk>\<^sub>2 (Q \<lbrakk>A\<rbrakk>\<^sub>2 R))"
  unfolding ParComp2TT_def 
proof auto
  fix x
  have "\<And> pa qa p q P Q R. x \<in> pa \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa \<Longrightarrow> p \<in> P \<Longrightarrow> pa \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q \<Longrightarrow> q \<in> Q \<Longrightarrow> qa \<in> R \<Longrightarrow>
    TT1 P \<Longrightarrow> TT1 Q \<Longrightarrow> TT1 R \<Longrightarrow>
    \<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> x \<in> xa"
  proof (induct x rule:ttWF.induct)
    fix P Q R :: "'a ttobs list set"
    fix pa qa p q
    assume TT1_P: "TT1 P" and TT1_Q: "TT1 Q" and TT1_R: "TT1 R"
    assume case_assms: "[] \<in> pa \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa" "p \<in> P" "pa \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q" "q \<in> Q" "qa \<in> R"
    then show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [] \<in> xa"
      apply (rule_tac x="{[]}" in exI, auto, rule_tac x="[]" in bexI)
      apply (rule_tac x="{[]}" in exI, auto, rule_tac x="[]" in bexI, rule_tac x="[]" in bexI)
      by (auto simp add: TT1_P TT1_Q TT1_R TT1_TT1w some_x_then_nil_TT1w)
  next
    fix P Q R :: "'a ttobs list set"
    fix X pa qa p q
    assume TT1_P: "TT1 P" and TT1_Q: "TT1 Q" and TT1_R: "TT1 R"
    assume case_assms: "[[X]\<^sub>R] \<in> pa \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa" "p \<in> P" "pa \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q" "q \<in> Q" "qa \<in> R"
    have pa_qa_cases: "(\<exists> Y Z. pa = [[Y]\<^sub>R] \<and> qa = [[Z]\<^sub>R])
        \<or> (\<exists> Y. pa = [[Y]\<^sub>R] \<and> qa = [[Tick]\<^sub>E])
        \<or> (\<exists> Z. pa = [[Tick]\<^sub>E] \<and> qa = [[Z]\<^sub>R])"
      using case_assms by (cases "(pa,qa)" rule:ttWF2.cases, auto)
    then show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [[X]\<^sub>R] \<in> xa"
    proof auto
      fix Y Z
      assume case_assms2: "pa = [[Y]\<^sub>R]" "qa = [[Z]\<^sub>R]"
      have p_q_cases: "(\<exists> Y2 Z2. p = [[Y2]\<^sub>R] \<and> q = [[Z2]\<^sub>R])
        \<or> (\<exists> Y2. p = [[Y2]\<^sub>R] \<and> q = [[Tick]\<^sub>E])
        \<or> (\<exists> Z2. p = [[Tick]\<^sub>E] \<and> q = [[Z2]\<^sub>R])"
        using case_assms case_assms2 by (cases "(p,q)" rule:ttWF2.cases, auto)
      then show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [[X]\<^sub>R] \<in> xa"
      proof auto
        fix Y2 Z2
        assume case_assms3: "p = [[Y2]\<^sub>R]" "q = [[Z2]\<^sub>R]"
        show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [[X]\<^sub>R] \<in> xa"
          using case_assms case_assms2 case_assms3 apply (rule_tac x="{[[X]\<^sub>R]}" in exI, simp)
          apply (rule_tac x="[[Y2]\<^sub>R]" in bexI, simp_all, rule_tac x="{[[Z2 \<union> Z]\<^sub>R]}" in exI, safe, simp_all)
          by (rule_tac x="[[Z2]\<^sub>R]" in bexI, simp_all, rule_tac x="[[Z]\<^sub>R]" in bexI, simp_all, blast+)
      next
        fix Y2
        assume case_assms3: "q = [[Tick]\<^sub>E]" "p = [[Y2]\<^sub>R]"
        show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [[X]\<^sub>R] \<in> xa"
          using case_assms case_assms2 case_assms3 apply (rule_tac x="{[[X]\<^sub>R]}" in exI, simp)
          apply (rule_tac x="[[Y2]\<^sub>R]" in bexI, simp_all)
          apply (rule_tac x="{W. \<exists> A'. A' \<subseteq> A \<and> W = [[Z \<union> Event ` A']\<^sub>R]}" in exI, safe, simp_all)
          apply (rule_tac x="[[Tick]\<^sub>E]" in bexI, simp_all, rule_tac x="[[Z]\<^sub>R]" in bexI, simp_all)
          by (rule_tac x="[[Z \<union> Event ` Aa]\<^sub>R]" in exI, simp_all, safe, blast+)
      next
        fix Z2
        assume case_assms3: "p = [[Tick]\<^sub>E]" "q = [[Z2]\<^sub>R]"
        show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [[X]\<^sub>R] \<in> xa"
          using case_assms case_assms2 case_assms3 apply simp
          apply (rule_tac x="{t. \<exists>A'. A' \<subseteq> A \<and> t = [[Z2 \<union> Z \<union> Event ` A']\<^sub>R]}" in exI, safe, simp_all)
          apply (rule_tac x="[[Tick]\<^sub>E]" in bexI, simp_all, rule_tac x="{[[Z2 \<union> Z]\<^sub>R]}" in exI, safe, simp_all)
          by (rule_tac x="[[Z2]\<^sub>R]" in bexI, simp_all, rule_tac x="[[Z]\<^sub>R]" in bexI, simp_all, blast+)
      qed
    next
      fix Y
      assume case_assms2: "qa = [[Tick]\<^sub>E]" "pa = [[Y]\<^sub>R]"
      have p_q_cases: "(\<exists> Y2 Z2. p = [[Y2]\<^sub>R] \<and> q = [[Z2]\<^sub>R])
        \<or> (\<exists> Y2. p = [[Y2]\<^sub>R] \<and> q = [[Tick]\<^sub>E])
        \<or> (\<exists> Z2. p = [[Tick]\<^sub>E] \<and> q = [[Z2]\<^sub>R])"
        using case_assms case_assms2 by (cases "(p,q)" rule:ttWF2.cases, auto)
      then show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [[X]\<^sub>R] \<in> xa"
      proof auto
        fix Y2 Z2
        assume case_assms3: "p = [[Y2]\<^sub>R]" "q = [[Z2]\<^sub>R]"
        show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [[X]\<^sub>R] \<in> xa"
          using case_assms case_assms2 case_assms3
          apply (rule_tac x="{[[X]\<^sub>R]}" in exI, simp,rule_tac x="[[Y2]\<^sub>R]" in bexI, safe)
          apply (rule_tac x="{t. \<exists>A'. A' \<subseteq> A \<and> t = [[Z2 \<union> Event ` A']\<^sub>R]}" in exI, safe, simp_all)
          apply (rule_tac x="[[Z2]\<^sub>R]" in bexI, simp_all,rule_tac x="[[Tick]\<^sub>E]" in bexI, simp_all)
          by (rule_tac x="[[Z2 \<union> Event ` Aa]\<^sub>R]" in exI, simp, blast)
      next
        fix Y2
        assume case_assms3: "q = [[Tick]\<^sub>E]" "p = [[Y2]\<^sub>R]"
        show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [[X]\<^sub>R] \<in> xa"
          using case_assms case_assms2 case_assms3
          apply (rule_tac x="{t. \<exists>A'. A' \<subseteq> A \<and> t = [[Y2 \<union> Event ` A']\<^sub>R]}" in exI, safe, simp_all)
          apply (rule_tac x="[[Y2]\<^sub>R]" in bexI, simp_all, rule_tac x="{[[Tick]\<^sub>E]}" in exI, safe, simp_all)
          apply (rule_tac x="[[Tick]\<^sub>E]" in bexI, simp_all, rule_tac x="[[Tick]\<^sub>E]" in bexI, safe, simp_all)
          by (metis Un_subset_iff image_Un sup_assoc)
      next
        fix Z2
        assume case_assms3: "p = [[Tick]\<^sub>E]" "q = [[Z2]\<^sub>R]"
        show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [[X]\<^sub>R] \<in> xa"
          using case_assms case_assms2 case_assms3 apply auto
          apply (rule_tac x="{t. \<exists>A'. A' \<subseteq> A \<and> t = [[Z2 \<union> Event ` A']\<^sub>R]}" in exI, safe, simp_all)
          apply (rule_tac x="[[Tick]\<^sub>E]" in bexI, simp_all)
          apply (rule_tac x="{t. \<exists>A'. A' \<subseteq> A \<and> t = [[Z2 \<union> Event ` A']\<^sub>R]}" in exI, safe, simp_all)
          apply (rule_tac x="[[Z2]\<^sub>R]" in bexI, simp_all, rule_tac x="[[Tick]\<^sub>E]" in bexI, simp_all)
          by (rule_tac x="[[Z2]\<^sub>R]" in exI, simp_all, blast, metis image_Un sup.absorb_iff2 sup_assoc)
      qed
    next
      fix Z
      assume case_assms2: "pa = [[Tick]\<^sub>E]" "qa = [[Z]\<^sub>R]"
      have p_q_cases: "p = [[Tick]\<^sub>E] \<and> q = [[Tick]\<^sub>E]"
        using case_assms case_assms2 by (cases "(p,q)" rule:ttWF2.cases, auto)
      then show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [[X]\<^sub>R] \<in> xa"
        using case_assms case_assms2 apply auto
        apply (rule_tac x="{t. \<exists>A'. A' \<subseteq> A \<and> t = [[Z \<union> Event ` A']\<^sub>R]}" in exI, safe, simp_all)
        apply (rule_tac x="[[Tick]\<^sub>E]" in bexI, simp_all)
        apply (rule_tac x="{t. \<exists>A'. A' \<subseteq> A \<and> t = [[Z \<union> Event ` A']\<^sub>R]}" in exI, safe, simp_all)
        apply (rule_tac x="[[Tick]\<^sub>E]" in bexI, simp_all, rule_tac x="[[Z]\<^sub>R]" in bexI, simp_all)
        by (rule_tac x="[[Z]\<^sub>R]" in exI, simp_all, blast+)
    qed
  next
    fix P Q R :: "'a ttobs list set"
    fix pa qa p q
    assume TT1_P: "TT1 P" and TT1_Q: "TT1 Q" and TT1_R: "TT1 R"
    assume case_assms: "[[Tick]\<^sub>E] \<in> pa \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa" "p \<in> P" "pa \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q" " q \<in> Q" "qa \<in> R"
    from case_assms have pa_qa_cases: "pa = [[Tick]\<^sub>E] \<and> qa = [[Tick]\<^sub>E]"
      by (cases "(pa,qa)" rule:ttWF2.cases, auto)
    from this and case_assms have p_q_cases: "p = [[Tick]\<^sub>E] \<and> q = [[Tick]\<^sub>E]"
      by (cases "(p,q)" rule:ttWF2.cases, auto)
    show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [[Tick]\<^sub>E] \<in> xa"
      using case_assms pa_qa_cases p_q_cases apply (rule_tac x="{[[Tick]\<^sub>E]}" in exI, simp)
      apply (rule_tac x="[[Tick]\<^sub>E]" in bexI, rule_tac x="{[[Tick]\<^sub>E]}" in exI, simp_all)
      by (rule_tac x="[[Tick]\<^sub>E]" in bexI, rule_tac x="[[Tick]\<^sub>E]" in bexI, simp_all)
  next
    fix P Q R :: "'a ttobs list set"
    fix pa qa p q e \<sigma>
    assume TT1_P: "TT1 P" and TT1_Q: "TT1 Q" and TT1_R: "TT1 R"
    assume ind_hyp: "\<And>pa qa p q P Q R. \<sigma> \<in> pa \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa \<Longrightarrow> p \<in> P \<Longrightarrow> pa \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q \<Longrightarrow> q \<in> Q \<Longrightarrow>
           qa \<in> R \<Longrightarrow> TT1 P \<Longrightarrow> TT1 Q \<Longrightarrow> TT1 R \<Longrightarrow>
           \<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> \<sigma> \<in> xa"
    assume case_assms: "[Event e]\<^sub>E # \<sigma> \<in> pa \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa" "p \<in> P" "pa \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q" "q \<in> Q" "qa \<in> R"
    then have pa_qa_cases: "(\<exists> pa' qa'. e \<in> A \<and> pa = [Event e]\<^sub>E # pa' \<and> qa = [Event e]\<^sub>E # qa' \<and> \<sigma> \<in> pa' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa')
        \<or> (\<exists> pa'. e \<notin> A \<and> pa = [Event e]\<^sub>E # pa' \<and> \<sigma> \<in> pa' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa)
        \<or> (\<exists> qa'. e \<notin> A \<and> qa = [Event e]\<^sub>E # qa' \<and> \<sigma> \<in> pa \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa')"
      by (cases "(pa,qa)" rule:ttWF2.cases, auto)
    then show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [Event e]\<^sub>E # \<sigma> \<in> xa"
    proof auto
      fix pa' qa'
      assume case_assms2: "e \<in> A" "pa = [Event e]\<^sub>E # pa'" "qa = [Event e]\<^sub>E # qa'" "\<sigma> \<in> pa' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa'"
      then have "(\<exists> p' q'. p = [Event e]\<^sub>E # p' \<and> q = [Event e]\<^sub>E # q' \<and> pa' \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
        using case_assms by (cases "(p,q)" rule:ttWF2.cases, auto)
      then show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [Event e]\<^sub>E # \<sigma> \<in> xa"
      proof auto
        fix p' q'
        assume case_assms3: "p = [Event e]\<^sub>E # p'" "q = [Event e]\<^sub>E # q'" "pa' \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q'"
        have "\<exists>xa. (\<exists>p\<in>{t. [Event e]\<^sub>E # t \<in> P}.
              \<exists>y. (\<exists>p\<in>{t. [Event e]\<^sub>E # t \<in> Q}. \<exists>q\<in>{t. [Event e]\<^sub>E # t \<in> R}. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and>
              (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> \<sigma> \<in> xa"
          using ind_hyp[where pa=pa', where qa=qa', where p=p', where q=q',
              where P="{t. [Event e]\<^sub>E # t \<in> P}", where Q="{t. [Event e]\<^sub>E # t \<in> Q}",
              where R="{t. [Event e]\<^sub>E # t \<in> R}"]
          case_assms case_assms2 case_assms3 by (auto simp add: TT1_P TT1_Q TT1_R TT1_init_event)
        then show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [Event e]\<^sub>E # \<sigma> \<in> xa"
          using case_assms case_assms2 case_assms3 apply auto
          apply (rule_tac x="[Event e]\<^sub>E # pb \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [Event e]\<^sub>E # qb" in exI, auto)
          apply (rule_tac x="[Event e]\<^sub>E # pb" in bexI, auto)
          apply (rule_tac x="[Event e]\<^sub>E # paa \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [Event e]\<^sub>E # qaa" in exI, auto)
          apply (rule_tac x="[Event e]\<^sub>E # paa" in bexI, auto)
          apply (rule_tac x="[Event e]\<^sub>E # qaa" in bexI, auto)
          done
      qed
    next
      fix pa'
      assume case_assms2: "e \<notin> A" "pa = [Event e]\<^sub>E # pa'" "\<sigma> \<in> pa' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa"
      have "(\<exists> p'. p = [Event e]\<^sub>E # p' \<and> pa' \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)
          \<or> (\<exists> q'. q = [Event e]\<^sub>E # q' \<and> pa' \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q')"
        using case_assms case_assms2 by (cases "(p,q)" rule:ttWF2.cases, auto)
      then show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [Event e]\<^sub>E # \<sigma> \<in> xa"
      proof auto
        fix p'
        assume case_assms3: "p = [Event e]\<^sub>E # p'" "pa' \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q"
        have "\<exists>xa. (\<exists>p\<in>{t. [Event e]\<^sub>E # t \<in> P}. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> \<sigma> \<in> xa"
          using ind_hyp[where pa=pa', where qa=qa, where p=p', where q=q,
              where P="{t. [Event e]\<^sub>E # t \<in> P}", where Q=Q, where R=R]
          case_assms case_assms2 case_assms3 by (auto simp add: TT1_P TT1_Q TT1_R TT1_init_event)
        then show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [Event e]\<^sub>E # \<sigma> \<in> xa"
          using case_assms case_assms2 case_assms3 apply auto
          by (rule_tac x="[Event e]\<^sub>E # pb \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qb" in exI, auto, case_tac qb rule:ttWF.cases, auto)
      next
        fix q'
        assume case_assms3: "q = [Event e]\<^sub>E # q'" "pa' \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q'"
        have "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>{t. [Event e]\<^sub>E # t \<in> Q}. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> \<sigma> \<in> xa"
          using ind_hyp[where pa=pa', where qa=qa, where p=p, where q=q',
              where P=P, where Q="{t. [Event e]\<^sub>E # t \<in> Q}", where R=R]
          case_assms case_assms2 case_assms3 by (auto simp add: TT1_P TT1_Q TT1_R TT1_init_event)
        then show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [Event e]\<^sub>E # \<sigma> \<in> xa"
          using case_assms case_assms2 case_assms3 apply auto
          apply (rule_tac x="pb \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [Event e]\<^sub>E # qb" in exI, auto, rule_tac x="pb" in bexI, auto)
          apply (rule_tac x="[Event e]\<^sub>E # paa \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qaa" in exI, auto, rule_tac x="[Event e]\<^sub>E # qb" in bexI, auto)
          by (case_tac qaa rule:ttWF.cases, auto, case_tac pb rule:ttWF.cases, auto)
      qed
    next
      fix qa'
      assume case_assms2: "e \<notin> A" "qa = [Event e]\<^sub>E # qa'" "\<sigma> \<in> pa \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa'"
      have "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>{t. [Event e]\<^sub>E # t \<in> R}. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> \<sigma> \<in> xa"
        using ind_hyp[where pa=pa, where qa=qa', where p=p, where q=q,
            where P=P, where Q=Q, where R="{t. [Event e]\<^sub>E # t \<in> R}"]
        case_assms case_assms2 by (auto simp add: TT1_P TT1_Q TT1_R TT1_init_event)
      then show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [Event e]\<^sub>E # \<sigma> \<in> xa"
        using case_assms case_assms2 apply auto
          apply (rule_tac x="pb \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [Event e]\<^sub>E # qb" in exI, auto, rule_tac x="pb" in bexI, auto)
          apply (rule_tac x="paa \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [Event e]\<^sub>E #  qaa" in exI, auto, rule_tac x="[Event e]\<^sub>E # qb" in bexI, auto)
        by (case_tac paa rule:ttWF.cases, auto, case_tac pb rule:ttWF.cases, auto)
    qed
  next
    fix P Q R :: "'a ttobs list set"
    fix X \<sigma> pa qa p q
    assume TT1_P: "TT1 P" and TT1_Q: "TT1 Q" and TT1_R: "TT1 R"
    assume ind_hyp: "\<And>pa qa p q P Q R. \<sigma> \<in> pa \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa \<Longrightarrow> p \<in> P \<Longrightarrow> pa \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q \<Longrightarrow>
      q \<in> Q \<Longrightarrow> qa \<in> R \<Longrightarrow> TT1 P \<Longrightarrow> TT1 Q \<Longrightarrow> TT1 R \<Longrightarrow>
      \<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> \<sigma> \<in> xa"
    assume case_assms: "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> pa \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa" "p \<in> P" "pa \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q" "q \<in> Q" "qa \<in> R"
    have pa_qa_cases:
      "(\<exists> Y Z pa' qa'. pa = [Y]\<^sub>R # [Tock]\<^sub>E # pa' \<and> qa = [Z]\<^sub>R # [Tock]\<^sub>E # qa' \<and> [[X]\<^sub>R] \<in> ([[Y]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Z]\<^sub>R]) \<and> \<sigma> \<in> (pa' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa'))
        \<or> (\<exists> Y pa'. pa = [Y]\<^sub>R # [Tock]\<^sub>E # pa' \<and> qa = [[Tick]\<^sub>E] \<and> [[X]\<^sub>R] \<in> ([[Y]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]) \<and> \<sigma> \<in> (pa' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa))
        \<or> (\<exists> Z qa'. qa = [Z]\<^sub>R # [Tock]\<^sub>E # qa' \<and> pa = [[Tick]\<^sub>E] \<and> [[X]\<^sub>R] \<in> ([[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Z]\<^sub>R]) \<and> \<sigma> \<in> (pa \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa'))"
      using case_assms by (cases "(pa,qa)" rule:ttWF2.cases, auto)
    then show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> xa"
    proof safe
      fix Y Z pa' qa'
      assume case_assms2: "pa = [Y]\<^sub>R # [Tock]\<^sub>E # pa'" "qa = [Z]\<^sub>R # [Tock]\<^sub>E # qa'"
        "[[X]\<^sub>R] \<in> [[Y]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Z]\<^sub>R]" "\<sigma> \<in> pa' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa'"
      have p_q_cases:
      "(\<exists> Y2 Z2 p' q'. p = [Y2]\<^sub>R # [Tock]\<^sub>E # p' \<and> q = [Z2]\<^sub>R # [Tock]\<^sub>E # q' \<and> [[Y]\<^sub>R] \<in> ([[Y2]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Z2]\<^sub>R]) \<and> pa' \<in> (p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q'))
        \<or> (\<exists> Y2 p'. p = [Y2]\<^sub>R # [Tock]\<^sub>E # p' \<and> q = [[Tick]\<^sub>E] \<and> [[Y]\<^sub>R] \<in> ([[Y2]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]) \<and> pa' \<in> (p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q))
        \<or> (\<exists> Z2 q'. q = [Z2]\<^sub>R # [Tock]\<^sub>E # q' \<and> p = [[Tick]\<^sub>E] \<and> [[Y]\<^sub>R] \<in> ([[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Z2]\<^sub>R]) \<and> pa' \<in> (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q'))"
        using case_assms case_assms2 by (cases "(p,q)" rule:ttWF2.cases, auto)
      then show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> xa"
      proof safe
        fix Y2 Z2 p' q'
        assume case_assms3: "p = [Y2]\<^sub>R # [Tock]\<^sub>E # p'" "q = [Z2]\<^sub>R # [Tock]\<^sub>E # q'"
          "[[Y]\<^sub>R] \<in> [[Y2]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Z2]\<^sub>R]" "pa' \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q'"
        have "\<exists>xa. (\<exists>p\<in>{t. [Y2]\<^sub>R # [Tock]\<^sub>E # t \<in> P}. \<exists>y. (\<exists>p\<in>{t. [Z2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}.
            \<exists>q\<in>{t. [Z]\<^sub>R # [Tock]\<^sub>E # t \<in> R}. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> \<sigma> \<in> xa"
          using ind_hyp[where pa=pa', where qa=qa', where p=p', where q=q',
              where P="{t. [Y2]\<^sub>R # [Tock]\<^sub>E # t \<in> P}", where Q="{t. [Z2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}",
              where R="{t. [Z]\<^sub>R # [Tock]\<^sub>E # t \<in> R}"]
              case_assms case_assms2 case_assms3 by (safe, simp_all add: TT1_P TT1_Q TT1_R TT1_init_tock)
        then show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> xa"
          using case_assms case_assms2 case_assms3 apply (safe, simp_all)
          apply (rule_tac x="[Y2]\<^sub>R # [Tock]\<^sub>E # pb \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [Z2 \<union> Z]\<^sub>R # [Tock]\<^sub>E # qb" in exI, simp_all, safe)
          apply (rule_tac x="[Y2]\<^sub>R # [Tock]\<^sub>E # pb" in bexI, simp_all)
          apply (rule_tac x="[Z2]\<^sub>R # [Tock]\<^sub>E # paa \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [Z]\<^sub>R # [Tock]\<^sub>E # qaa" in exI, simp_all, safe)
          apply (rule_tac x="[Z2]\<^sub>R # [Tock]\<^sub>E # paa" in bexI, simp_all)
          apply (rule_tac x="[Z]\<^sub>R # [Tock]\<^sub>E # qaa" in bexI, simp_all, blast)
          apply (rule_tac x="[Z \<union> Z2]\<^sub>R # [Tock]\<^sub>E # qb" in exI, simp_all, blast+)
          done
      next
        fix Y2 p'
        assume case_assms3: "p = [Y2]\<^sub>R # [Tock]\<^sub>E # p'" "q = [[Tick]\<^sub>E]" "[[Y]\<^sub>R] \<in> [[Y2]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]"
        have "TT1 {[], [[Tick]\<^sub>E]}"
          using TT_Skip unfolding TT_def SkipTT_def by auto
        then have "\<exists>xa. (\<exists>p\<in>{t. [Y2]\<^sub>R # [Tock]\<^sub>E # t \<in> P}. \<exists>y. (\<exists>p\<in>{[], [[Tick]\<^sub>E]}.
          \<exists>q\<in>{t. [Z]\<^sub>R # [Tock]\<^sub>E # t \<in> R}. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> \<sigma> \<in> xa"
          using ind_hyp[where pa=pa', where qa=qa', where p=p', where q=q,
              where P="{t. [Y2]\<^sub>R # [Tock]\<^sub>E # t \<in> P}", where Q="{[], [[Tick]\<^sub>E]}", where R="{t. [Z]\<^sub>R # [Tock]\<^sub>E # t \<in> R}"]
          case_assms case_assms2 case_assms3 by (auto simp add: TT1_P TT1_R TT1_init_tock)
        then have "\<exists>xa. (\<exists>p\<in>{t. [Y2]\<^sub>R # [Tock]\<^sub>E # t \<in> P}. \<exists>y. (\<exists>q\<in>{t. [Z]\<^sub>R # [Tock]\<^sub>E # t \<in> R}. y = [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> \<sigma> \<in> xa"
        proof auto
          fix p q qa
          assume inner_assms: "\<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q" "[Y2]\<^sub>R # [Tock]\<^sub>E # p \<in> P" "q \<in> [] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa" "[Z]\<^sub>R # [Tock]\<^sub>E # qa \<in> R"
          then obtain qa' where "qa' \<lesssim>\<^sub>C qa" "q \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa'"
            using merge_traces2_empty1_prefix_subset_merge_traces2_Tick1 by force
          then show "\<exists>xa. (\<exists>p. [Y2]\<^sub>R # [Tock]\<^sub>E # p \<in> P \<and>
                 (\<exists>y. (\<exists>q. [Z]\<^sub>R # [Tock]\<^sub>E # q \<in> R \<and> y = [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q))) \<and> \<sigma> \<in> xa"
            using inner_assms apply (rule_tac x="p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q" in exI, auto)
            apply (rule_tac x="p" in exI, auto)
            apply (rule_tac x="[[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa'" in exI, auto)
            apply (rule_tac x="qa'" in exI, auto)
            by (meson TT1_R TT1_def tt_prefix_subset.simps(2) tt_prefix_subset.simps(3) tt_prefix_subset_refl)
        qed
        then show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> xa"
          using case_assms case_assms2 case_assms3 apply (safe, simp_all, safe)
          apply (rule_tac x="[Y2]\<^sub>R # [Tock]\<^sub>E # pb \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [Z \<union> Event ` Aa]\<^sub>R # [Tock]\<^sub>E # qaa" in exI, simp_all, safe)
          apply (rule_tac x="[Y2]\<^sub>R # [Tock]\<^sub>E # pb" in bexI, simp_all)
          apply (rule_tac x="[[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [Z]\<^sub>R # [Tock]\<^sub>E # qb" in exI, safe)
          apply (rule_tac x="[[Tick]\<^sub>E]" in bexI, simp_all)
          apply (rule_tac x="[Z]\<^sub>R # [Tock]\<^sub>E # qb" in bexI, simp_all)
          apply (rule_tac x="[Z \<union> Event ` Aa]\<^sub>R # [Tock]\<^sub>E # qaa" in exI, simp_all, blast+)
          done
      next
        fix Z2 q'
        assume case_assms3: "q = [Z2]\<^sub>R # [Tock]\<^sub>E # q'" "p = [[Tick]\<^sub>E]"
          "[[Y]\<^sub>R] \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Z2]\<^sub>R]" "pa' \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q'"
        have "TT1 {[], [[Tick]\<^sub>E]}"
          using TT_Skip unfolding TT_def SkipTT_def by auto
        then have "\<exists>xa. (\<exists>p\<in>{[], [[Tick]\<^sub>E]}. \<exists>y. (\<exists>p\<in>{t. [Z2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}.
            \<exists>q\<in>{t. [Z]\<^sub>R # [Tock]\<^sub>E # t \<in> R}. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> \<sigma> \<in> xa"
          using ind_hyp[where pa=pa', where qa=qa', where p="[[Tick]\<^sub>E]", where q=q', 
              where P="{[], [[Tick]\<^sub>E]}", where Q="{t. [Z2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}", where R="{t. [Z]\<^sub>R # [Tock]\<^sub>E # t \<in> R}"]
            case_assms case_assms2 case_assms3 by (auto simp add: TT1_Q TT1_R TT1_init_tock)
        then have "\<exists>xa. (\<exists>y. (\<exists>p\<in>{t. [Z2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}.
            \<exists>q\<in>{t. [Z]\<^sub>R # [Tock]\<^sub>E # t \<in> R}. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> \<sigma> \<in> xa"
        proof auto
          fix q p qa
          assume inner_assms: "\<sigma> \<in> [] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q" "q \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa" "[Z2]\<^sub>R # [Tock]\<^sub>E # p \<in> Q" "[Z]\<^sub>R # [Tock]\<^sub>E # qa \<in> R"
          obtain q' where q'_assms: "q' \<lesssim>\<^sub>C q \<and> \<sigma> \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q'"
            using inner_assms merge_traces2_empty1_prefix_subset_merge_traces2_Tick1 by blast
          then obtain p' qa' where p'_qa'_assms: "p' \<lesssim>\<^sub>C p \<and> qa' \<lesssim>\<^sub>C qa \<and> q' \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa'"
            using inner_assms merge_traces2_prefix_subset by blast 
          then show "\<exists>xa. (\<exists>y. (\<exists>p. [Z2]\<^sub>R # [Tock]\<^sub>E # p \<in> Q \<and> (\<exists>q. [Z]\<^sub>R # [Tock]\<^sub>E # q \<in> R \<and> y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and>
                 (\<exists>q\<in>y. xa = [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> \<sigma> \<in> xa"
            using inner_assms q'_assms p'_qa'_assms apply (rule_tac x="[[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q'" in exI, auto)
            apply (rule_tac x="p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa'" in exI, auto, rule_tac x="p'" in exI, auto)
            apply (meson TT1_Q TT1_def subset_iff tt_prefix_subset.simps(2) tt_prefix_subset.simps(3))
            by (rule_tac x="qa'" in exI, auto, meson TT1_R TT1_def equalityE tt_prefix_subset.simps(2) tt_prefix_subset.simps(3))
        qed
        then show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> xa"
          using case_assms case_assms2 case_assms3 apply (simp_all, safe)
          apply (rule_tac x="[[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [Z2 \<union> Z]\<^sub>R # [Tock]\<^sub>E # qb" in exI, simp, safe)
          apply (rule_tac x="[[Tick]\<^sub>E]" in bexI, simp_all)
          apply (rule_tac x="[Z2]\<^sub>R # [Tock]\<^sub>E # pb \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [Z]\<^sub>R # [Tock]\<^sub>E # qc" in exI, safe)
          apply (rule_tac x="[Z2]\<^sub>R # [Tock]\<^sub>E # pb" in bexI, simp)
          apply (rule_tac x="[Z]\<^sub>R # [Tock]\<^sub>E # qc" in bexI, simp, blast, blast)
          by (rule_tac x="[Z2 \<union> Z]\<^sub>R # [Tock]\<^sub>E # qb" in bexI, simp_all, blast+)
      qed
    next
      fix Y pa'
      assume case_assms2: "pa = [Y]\<^sub>R # [Tock]\<^sub>E # pa'" "qa = [[Tick]\<^sub>E]"
        "[[X]\<^sub>R] \<in> [[Y]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]" "\<sigma> \<in> pa' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]"
      have p_q_cases:
        "(\<exists> Y2 Z2 p' q'. p = [Y2]\<^sub>R # [Tock]\<^sub>E # p' \<and> q = [Z2]\<^sub>R # [Tock]\<^sub>E # q' \<and> [[Y]\<^sub>R] \<in> ([[Y2]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Z2]\<^sub>R]) \<and> pa' \<in> (p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q'))
        \<or> (\<exists> Y2 p'. p = [Y2]\<^sub>R # [Tock]\<^sub>E # p' \<and> q = [[Tick]\<^sub>E] \<and> [[Y]\<^sub>R] \<in> ([[Y2]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]) \<and> pa' \<in> (p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q))
        \<or> (\<exists> Z2 q'. q = [Z2]\<^sub>R # [Tock]\<^sub>E # q' \<and> p = [[Tick]\<^sub>E] \<and> [[Y]\<^sub>R] \<in> ([[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Z2]\<^sub>R]) \<and> pa' \<in> (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q'))"
        using case_assms case_assms2 by (cases "(p,q)" rule:ttWF2.cases, simp_all)
      then show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> xa"
      proof (safe, simp_all)
        fix Y2 Z2 p' q'
        assume case_assms3: " p = [Y2]\<^sub>R # [Tock]\<^sub>E # p'" "q = [Z2]\<^sub>R # [Tock]\<^sub>E # q'" "pa' \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q'"
          "Y = Y2 \<union> Z2 \<and> {e \<in> Z2. e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A} = {e \<in> Y2. e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A}"
        have "TT1 {[], [[Tick]\<^sub>E]}"
          using TT_Skip unfolding TT_def SkipTT_def by auto
        then have "\<exists>xa. (\<exists>p\<in>{t. [Y2]\<^sub>R # [Tock]\<^sub>E # t \<in> P}. \<exists>y. (\<exists>p\<in>{t. [Z2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}.
          \<exists>q\<in>{[], [[Tick]\<^sub>E]}. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> \<sigma> \<in> xa"
          using ind_hyp[where pa=pa', where qa=qa, where p=p', where q=q',
            where P="{t. [Y2]\<^sub>R # [Tock]\<^sub>E # t \<in> P}", where Q="{t. [Z2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}", where R="{[], [[Tick]\<^sub>E]}"]
            case_assms case_assms2 case_assms3 by (simp add: TT1_P TT1_Q TT1_init_tock, blast)
        then have "\<exists>xa. (\<exists>p\<in>{t. [Y2]\<^sub>R # [Tock]\<^sub>E # t \<in> P}. \<exists>y. (\<exists>p\<in>{t. [Z2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}.
           y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> \<sigma> \<in> xa"
        proof auto
          fix p q pa
          assume inner_assms: "\<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q" "[Y2]\<^sub>R # [Tock]\<^sub>E # p \<in> P" "q \<in> pa \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 []" "[Z2]\<^sub>R # [Tock]\<^sub>E # pa \<in> Q"
          then obtain pa' where "pa' \<lesssim>\<^sub>C pa \<and> q \<in> pa' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]"
            using merge_traces2_empty2_prefix_subset_merge_traces2_Tick2 by blast
          then show "\<exists>xa. (\<exists>p. [Y2]\<^sub>R # [Tock]\<^sub>E # p \<in> P \<and> (\<exists>y. (\<exists>p. [Z2]\<^sub>R # [Tock]\<^sub>E # p \<in> Q \<and>
              y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q))) \<and> \<sigma> \<in> xa"
            using inner_assms apply (rule_tac x="p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q" in exI, auto, rule_tac x="p" in exI, auto)
            apply (rule_tac x="pa' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]" in exI, auto, rule_tac x="pa'" in exI, auto)
            by (meson TT1_Q TT1_def equalityE tt_prefix_subset.simps(2) tt_prefix_subset.simps(3))
        qed
        then show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> xa"
          using case_assms case_assms2 case_assms3 apply (safe, simp_all, safe)
          apply (rule_tac x="[Y2]\<^sub>R # [Tock]\<^sub>E # pb \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [Z2 \<union> Event ` Aa]\<^sub>R # [Tock]\<^sub>E # qb" in exI, safe, simp_all)
          apply (rule_tac x="[Y2]\<^sub>R # [Tock]\<^sub>E # pb" in bexI, safe, simp_all)
          apply (rule_tac x="[Z2]\<^sub>R # [Tock]\<^sub>E # paa \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]" in exI, safe, simp_all)
          apply (rule_tac x="[Z2]\<^sub>R # [Tock]\<^sub>E # paa" in bexI, simp_all)
          apply (rule_tac x="[[Tick]\<^sub>E]" in bexI, safe, simp_all, blast)
          by (rule_tac x="[Z2 \<union> Event ` Aa]\<^sub>R # [Tock]\<^sub>E # qb" in exI, auto)
      next
        fix Y2 p'
        assume case_assms3: "p = [Y2]\<^sub>R # [Tock]\<^sub>E # p'" "q = [[Tick]\<^sub>E]" "\<exists>Aa\<subseteq>A. Y = Y2 \<union> Event ` Aa"
          "pa' \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]"
        have "TT1 {[], [[Tick]\<^sub>E]}"
          using TT_Skip unfolding SkipTT_def TT_def by auto
        then have "\<exists>xa. (\<exists>p\<in>{t. [Y2]\<^sub>R # [Tock]\<^sub>E # t \<in> P}. \<exists>y. (\<exists>p\<in>{[], [[Tick]\<^sub>E]}.
          \<exists>q\<in>{[], [[Tick]\<^sub>E]}. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> \<sigma> \<in> xa"
          using ind_hyp[where pa=pa', where qa="[[Tick]\<^sub>E]", where p=p', where q="[[Tick]\<^sub>E]",
              where P="{t. [Y2]\<^sub>R # [Tock]\<^sub>E # t \<in> P}", where Q="{[], [[Tick]\<^sub>E]}", where R="{[], [[Tick]\<^sub>E]}"]
              case_assms case_assms2 case_assms3 by (auto simp add: TT1_P TT1_init_tock)
        then have "\<exists>xa. (\<exists>p\<in>{t. [Y2]\<^sub>R # [Tock]\<^sub>E # t \<in> P}. \<exists>y. (y =  [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E])
          \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> \<sigma> \<in> xa"
        proof auto
          fix p
          assume inner_assms: "\<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 []" "[Y2]\<^sub>R # [Tock]\<^sub>E # p \<in> P"
          then obtain p' where "p' \<lesssim>\<^sub>C p \<and> \<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]"
            using merge_traces2_empty2_prefix_subset_merge_traces2_Tick2 by blast
          then show "\<exists>xa. (\<exists>p. [Y2]\<^sub>R # [Tock]\<^sub>E # p \<in> P \<and> xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]) \<and> \<sigma> \<in> xa"
            using inner_assms apply (rule_tac x="p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]" in exI, auto, rule_tac x="p'" in exI, auto)
            by (meson TT1_P TT1_def equalityE tt_prefix_subset.simps(2) tt_prefix_subset.simps(3))
        qed
        then show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> xa"
          using case_assms case_assms2 case_assms3 apply auto
          apply (rule_tac x="[Y2]\<^sub>R # [Tock]\<^sub>E # pb \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]" in exI, safe, simp_all)
          apply (rule_tac x="[Y2]\<^sub>R # [Tock]\<^sub>E # pb" in bexI, simp_all, rule_tac x="{[[Tick]\<^sub>E]}" in exI, simp_all)
          apply (rule_tac x="[[Tick]\<^sub>E]" in bexI, rule_tac x="[[Tick]\<^sub>E]" in bexI, simp_all)
          by (metis Un_subset_iff image_Un sup_assoc)
      next
        fix Z2 q'
        assume case_assms3: "q = [Z2]\<^sub>R # [Tock]\<^sub>E # q'" "p = [[Tick]\<^sub>E]" "\<exists>Aa\<subseteq>A. Y = Z2 \<union> Event ` Aa"
          "pa' \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q'"
        have "TT1 {[], [[Tick]\<^sub>E]}"
          using TT_Skip unfolding SkipTT_def TT_def by auto
        then have "\<exists>xa. (\<exists>p\<in>{[], [[Tick]\<^sub>E]}. \<exists>y. (\<exists>p\<in>{t. [Z2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}.
            \<exists>q\<in>{[], [[Tick]\<^sub>E]}. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> \<sigma> \<in> xa"
          using ind_hyp[where pa=pa', where qa ="[[Tick]\<^sub>E]", where p ="[[Tick]\<^sub>E]", where q =q', 
              where P="{[], [[Tick]\<^sub>E]}", where Q="{t. [Z2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}", where R="{[], [[Tick]\<^sub>E]}"]
              case_assms case_assms2 case_assms3 by (auto, smt merge_traces2_comm)
        then have "\<exists>xa. (\<exists>y. (\<exists>p\<in>{t. [Z2]\<^sub>R # [Tock]\<^sub>E # t \<in> Q}. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E])
            \<and> (\<exists>q\<in>y. xa = [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> \<sigma> \<in> xa"
        proof auto
          fix q p
          assume inner_assms: "\<sigma> \<in> [] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q" "q \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 []" "[Z2]\<^sub>R # [Tock]\<^sub>E # p \<in> Q"
          obtain q' where q'_assms: "q' \<lesssim>\<^sub>C q \<and> \<sigma> \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q'"
            using inner_assms(1) merge_traces2_empty1_prefix_subset_merge_traces2_Tick1 by blast
          have "\<exists> p'. p' \<lesssim>\<^sub>C p \<and> q' \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 []"
            using inner_assms(2) merge_traces2_prefix_subset q'_assms tt_prefix_subset.simps(1) tt_prefix_subset_antisym by blast
          then obtain p' where p'_assms: "p' \<lesssim>\<^sub>C p \<and> q' \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]"
            by (meson merge_traces2_empty2_prefix_subset_merge_traces2_Tick2 tt_prefix_subset_trans)
          show "\<exists>xa. (\<exists>y. (\<exists>p. [Z2]\<^sub>R # [Tock]\<^sub>E # p \<in> Q \<and> y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]) \<and> (\<exists>q\<in>y. xa = [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> \<sigma> \<in> xa"
            using inner_assms p'_assms q'_assms apply (auto, rule_tac x="[[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q'" in exI, auto)
            apply (rule_tac x="p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]" in exI, auto, rule_tac x="p'" in exI, auto)
            by (meson TT1_Q TT1_def equalityE tt_prefix_subset.simps(2) tt_prefix_subset.simps(3))
        next
          fix q p
          assume inner_assms: "\<sigma> \<in> [] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q" "q \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]" "[Z2]\<^sub>R # [Tock]\<^sub>E # p \<in> Q"
          obtain q' where q'_assms: "q' \<lesssim>\<^sub>C q \<and> \<sigma> \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q'"
            using inner_assms(1) merge_traces2_empty1_prefix_subset_merge_traces2_Tick1 by blast
          have "\<exists> p' a. p' \<lesssim>\<^sub>C p \<and> q' \<in> (p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 a) \<and> a \<in> {[], [[Tick]\<^sub>E]}"
            by (meson TT1_def \<open>TT1 {[], [[Tick]\<^sub>E]}\<close> inner_assms(2) insertCI merge_traces2_prefix_subset q'_assms)
          then obtain p' where p'_assms: "p' \<lesssim>\<^sub>C p \<and> q' \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]"
            by (auto, meson merge_traces2_empty2_prefix_subset_merge_traces2_Tick2 tt_prefix_subset_trans)
          show "\<exists>xa. (\<exists>y. (\<exists>p. [Z2]\<^sub>R # [Tock]\<^sub>E # p \<in> Q \<and> y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]) \<and> (\<exists>q\<in>y. xa = [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> \<sigma> \<in> xa"
            using inner_assms p'_assms q'_assms apply (auto, rule_tac x="[[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q'" in exI, auto)
            apply (rule_tac x="p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]" in exI, auto, rule_tac x="p'" in exI, auto)
            by (meson TT1_Q TT1_def equalityE tt_prefix_subset.simps(2) tt_prefix_subset.simps(3))
        next
          fix q p
          assume inner_assms: "\<sigma> \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q" "q \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 []" "[Z2]\<^sub>R # [Tock]\<^sub>E # p \<in> Q"
          then obtain p' where p'_assms: "p' \<lesssim>\<^sub>C p \<and> q \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]"
            using merge_traces2_empty2_prefix_subset_merge_traces2_Tick2 by blast
          show "\<exists>xa. (\<exists>y. (\<exists>p. [Z2]\<^sub>R # [Tock]\<^sub>E # p \<in> Q \<and> y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]) \<and> (\<exists>q\<in>y. xa = [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> \<sigma> \<in> xa"
            using inner_assms p'_assms apply (auto, rule_tac x="[[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q" in exI, auto)
            apply (rule_tac x="p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]" in exI, auto, rule_tac x="p'" in exI, auto)
            by (meson TT1_Q TT1_def equalityE tt_prefix_subset.simps(2) tt_prefix_subset.simps(3))
        qed
        then show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> xa"
          using case_assms case_assms2 case_assms3 apply auto
          apply (rule_tac x="[[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [Z2]\<^sub>R # [Tock]\<^sub>E # qb" in exI, safe, simp_all)
          apply (rule_tac x="[[Tick]\<^sub>E]" in bexI, simp_all)
          apply (rule_tac x="[Z2]\<^sub>R # [Tock]\<^sub>E # pb \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]" in exI, safe, simp_all)
          apply (rule_tac x="[Z2]\<^sub>R # [Tock]\<^sub>E # pb" in bexI, simp_all, rule_tac x="[[Tick]\<^sub>E]" in bexI, simp_all)
          by (rule_tac x="[Z2]\<^sub>R # [Tock]\<^sub>E # qb" in exI, simp_all, blast, rule_tac x="Aa \<union> Aaa" in exI, auto)
      qed
    next
      fix Z qa'
      assume case_assms2: "qa = [Z]\<^sub>R # [Tock]\<^sub>E # qa'" "pa = [[Tick]\<^sub>E]"
        "[[X]\<^sub>R] \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [[Z]\<^sub>R]" "\<sigma> \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa'"
      then have p_q_assms: "p = [[Tick]\<^sub>E] \<and> q = [[Tick]\<^sub>E]"
        using case_assms by (cases "(p,q)" rule:ttWF2.cases, auto)
      have "\<And> \<sigma>. \<sigma> \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa' \<Longrightarrow> \<exists> qa''. qa'' \<lesssim>\<^sub>C qa' \<and> qa' \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa''"
        apply (induct qa' rule:ttWF.induct, auto, rule_tac x="[]" in exI, auto)
      proof (rule_tac x="[[X]\<^sub>R]" in exI, auto, rule_tac x="[[Tick]\<^sub>E]" in exI, auto)
        fix e \<sigma> s
        assume ind_hyp: "\<And>\<sigma>'. \<sigma>' \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 \<sigma> \<Longrightarrow> \<exists>qa''. qa'' \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa''"
        assume inner_assms: "e \<notin> A" "s \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 \<sigma>"
        then have "\<exists>qa''. qa'' \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa''"
          using ind_hyp by auto
        then show "\<exists>qa''. qa'' \<lesssim>\<^sub>C [Event e]\<^sub>E # \<sigma> \<and> [Event e]\<^sub>E # \<sigma> \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa''"
          using inner_assms by (auto, rule_tac x="[Event e]\<^sub>E # qa''" in exI, auto)
      next
        fix X \<sigma> Aa s
        assume ind_hyp: "\<And>\<sigma>'. \<sigma>' \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 \<sigma> \<Longrightarrow> \<exists>qa''. qa'' \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa''"
        assume inner_assms: "Aa \<subseteq> A" "s \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 \<sigma>"
        then have "\<exists>qa''. qa'' \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa''"
          using ind_hyp by auto
        then show "\<exists>qa''. qa'' \<lesssim>\<^sub>C [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa''"
          using inner_assms by (auto, rule_tac x="[X]\<^sub>R # [Tock]\<^sub>E # qa''" in exI, auto)
      qed
      then obtain qa'' where "qa'' \<lesssim>\<^sub>C qa' \<and> qa' \<in> [[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa''"
        using case_assms2(4) by blast
      then show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> xa"
        using p_q_assms case_assms case_assms2 apply auto
        apply (rule_tac x="[[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [Z]\<^sub>R # [Tock]\<^sub>E # qa'" in exI, auto, rule_tac x="[[Tick]\<^sub>E]" in bexI, auto)
        apply (rule_tac x="[[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 [Z]\<^sub>R # [Tock]\<^sub>E # qa''" in exI, auto, rule_tac x="[[Tick]\<^sub>E]" in bexI, auto)
        apply (rule_tac x="[Z]\<^sub>R # [Tock]\<^sub>E # qa''" in bexI, auto)
        apply (meson TT1_R TT1_def equalityE tt_prefix_subset.simps(2) tt_prefix_subset.simps(3))
        by (rule_tac x="[Z]\<^sub>R # [Tock]\<^sub>E # qa'" in exI, auto)
    qed
  next
    fix va pa qa p q P Q R
    assume "[Tock]\<^sub>E # va \<in> pa \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa"
    then show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [Tock]\<^sub>E # va \<in> xa"
      by (cases "(pa,qa)" rule:ttWF2.cases, auto)
  next
    fix va pa qa p q P Q R
    assume "[Tock]\<^sub>E # va \<in> pa \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa"
    then show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [Tock]\<^sub>E # va \<in> xa"
      by (cases "(pa,qa)" rule:ttWF2.cases, auto)
  next
    fix va pa qa p q P Q R
    assume "[Tock]\<^sub>E # va \<in> pa \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa"
    then show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [Tock]\<^sub>E # va \<in> xa"
      by (cases "(pa,qa)" rule:ttWF2.cases, auto)
  next
    fix v vc pa qa p q P Q R
    assume "[Tick]\<^sub>E # v # vc \<in> pa \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa"
    then show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [Tick]\<^sub>E # v # vc \<in> xa"
      by (cases "(pa,qa)" rule:ttWF2.cases, auto)
  next
    fix v vc pa qa p q P Q R
    assume "[Tick]\<^sub>E # v # vc \<in> pa \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa"
    then show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [Tick]\<^sub>E # v # vc \<in> xa"
      by (cases "(pa,qa)" rule:ttWF2.cases, auto)
  next
    fix va vd vc pa qa p q P Q R
    assume "[va]\<^sub>R # [Event vd]\<^sub>E # vc \<in> pa \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa"
    then show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [va]\<^sub>R # [Event vd]\<^sub>E # vc \<in> xa"
      by (cases "(pa,qa)" rule:ttWF2.cases, auto)
  next
    fix va vc pa qa p q P Q R
    assume "[va]\<^sub>R # [Tick]\<^sub>E # vc \<in> pa \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa"
    then show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [va]\<^sub>R # [Tick]\<^sub>E # vc \<in> xa"
      by (cases "(pa,qa)" rule:ttWF2.cases, auto)
  next
    fix va v vc pa qa p q P Q R
    assume "[va]\<^sub>R # [v]\<^sub>R # vc \<in> pa \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa"
    then show "\<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> [va]\<^sub>R # [v]\<^sub>R # vc \<in> xa"
      by (cases "(pa,qa)" rule:ttWF2.cases, auto)
  qed
  then show "\<And> p pa q qa. x \<in> pa \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 qa \<Longrightarrow> p \<in> P \<Longrightarrow> pa \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q \<Longrightarrow> q \<in> Q \<Longrightarrow> qa \<in> R \<Longrightarrow>
    \<exists>xa. (\<exists>p\<in>P. \<exists>y. (\<exists>p\<in>Q. \<exists>q\<in>R. y = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q) \<and> (\<exists>q\<in>y. xa = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> x \<in> xa"
    using assms by auto
qed

lemma ParComp2_assoc_subset2:
  assumes "TT1 P" "TT1 Q" "TT1 R"
  shows "(P \<lbrakk>A\<rbrakk>\<^sub>2 (Q \<lbrakk>A\<rbrakk>\<^sub>2 R)) \<subseteq> ((P \<lbrakk>A\<rbrakk>\<^sub>2 Q) \<lbrakk>A\<rbrakk>\<^sub>2 R)"
  (is "?lhs \<subseteq> ?rhs")
proof -
  have "?lhs \<subseteq> ((Q \<lbrakk>A\<rbrakk>\<^sub>2 R) \<lbrakk>A\<rbrakk>\<^sub>2 P)"
    by (simp add: ParComp2_comm)
  also have "... \<subseteq> (Q \<lbrakk>A\<rbrakk>\<^sub>2 (R \<lbrakk>A\<rbrakk>\<^sub>2 P))"
    by (simp add: ParComp2_assoc_subset1 assms)
  also have "... \<subseteq> ((R \<lbrakk>A\<rbrakk>\<^sub>2 P) \<lbrakk>A\<rbrakk>\<^sub>2 Q)"
    by (simp add: ParComp2_comm)
  also have "... \<subseteq> (R \<lbrakk>A\<rbrakk>\<^sub>2 (P \<lbrakk>A\<rbrakk>\<^sub>2 Q))"
    by (simp add: ParComp2_assoc_subset1 assms)
  also have "... \<subseteq> ((P \<lbrakk>A\<rbrakk>\<^sub>2 Q) \<lbrakk>A\<rbrakk>\<^sub>2 R)"
    by (simp add: ParComp2_comm)
  then show ?thesis
    using calculation by auto
qed

lemma ParComp2_assoc:
  assumes "TT1 P" "TT1 Q" "TT1 R"
  shows "(P \<lbrakk>A\<rbrakk>\<^sub>2 (Q \<lbrakk>A\<rbrakk>\<^sub>2 R)) = ((P \<lbrakk>A\<rbrakk>\<^sub>2 Q) \<lbrakk>A\<rbrakk>\<^sub>2 R)"
  using ParComp2_assoc_subset1 ParComp2_assoc_subset2 assms by blast

lemma ParComp2_Skip_right_unit:
  assumes "\<forall>x\<in>P. ttWF x" "TT1 P"
  shows "(P \<lbrakk>{}\<rbrakk>\<^sub>2 SKIP\<^sub>C) = P"
  using assms unfolding ParComp2TT_def SkipTT_def
proof auto
  fix x p :: "'a ttobs list"
  show "\<And> P. TT1 P \<Longrightarrow> x \<in> p \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 [] \<Longrightarrow> p \<in> P \<Longrightarrow> x \<in> P"
  proof (induct x p rule:ttWF2.induct, auto)
    fix Y and P :: "'a ttobs list set"
    show "TT1 P \<Longrightarrow> [[Y]\<^sub>R] \<in> P \<Longrightarrow> [] \<in> P"
      unfolding TT1_def by force
  next
    fix P :: "'a ttobs list set"
    show "TT1 P \<Longrightarrow> [[Tick]\<^sub>E] \<in> P \<Longrightarrow> [] \<in> P"
      unfolding TT1_def by force
  next
    fix P :: "'a ttobs list set"
    fix \<rho> \<sigma> :: "'a ttobs list"
    fix f 
    assume ind_hyp: "\<And>P. TT1 P \<Longrightarrow> \<sigma> \<in> P \<Longrightarrow> \<rho> \<in> P"
    assume case_assms: "TT1 P" "[Event f]\<^sub>E # \<sigma> \<in> P" "\<rho> \<in> \<sigma> \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 []"
    then have "TT1 {t. [Event f]\<^sub>E # t \<in> P}"
      by (simp add: TT1_init_event)
    then have "\<rho> \<in> {t. [Event f]\<^sub>E # t \<in> P}"
      using case_assms ind_hyp[where P="{t. [Event f]\<^sub>E # t \<in> P}"] by auto
    then show "[Event f]\<^sub>E # \<rho> \<in> P"
      by auto
  next
    fix X \<rho> \<sigma> and P :: "'a ttobs list set"
    show "[X]\<^sub>R # [Tick]\<^sub>E # \<rho> \<in> \<sigma> \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 [] \<Longrightarrow> [X]\<^sub>R # [Tick]\<^sub>E # \<rho> \<in> P"
      by (cases \<sigma> rule:ttWF.cases, auto)
  next
    fix X e \<rho> \<sigma> and P :: "'a ttobs list set"
    show "[X]\<^sub>R # [Event e]\<^sub>E # \<rho> \<in> \<sigma> \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 [] \<Longrightarrow> [X]\<^sub>R # [Event e]\<^sub>E # \<rho> \<in> P"
      by (cases \<sigma> rule:ttWF.cases, auto)
  next
    fix X Y \<rho> \<sigma> and P :: "'a ttobs list set"
    show "[X]\<^sub>R # [Y]\<^sub>R # \<rho> \<in> \<sigma> \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 [] \<Longrightarrow> [X]\<^sub>R # [Y]\<^sub>R # \<rho> \<in> P"
      by (cases \<sigma> rule:ttWF.cases, auto)
  next
    fix x \<rho> \<sigma> and P :: "'a ttobs list set"
    show "[Tick]\<^sub>E # x # \<rho> \<in> \<sigma> \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 [] \<Longrightarrow> [Tick]\<^sub>E # x # \<rho> \<in> P"
      by (cases \<sigma> rule:ttWF.cases, auto)
  next
    fix \<rho> \<sigma> and P :: "'a ttobs list set"
    show "[Tock]\<^sub>E # \<rho> \<in> \<sigma> \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 [] \<Longrightarrow> [Tock]\<^sub>E # \<rho> \<in> P"
      by (cases \<sigma> rule:ttWF.cases, auto)
  qed
next
  fix x p :: "'a ttobs list"
  show "\<And>P. x \<in> p \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E] \<Longrightarrow> p \<in> P \<Longrightarrow> x \<in> P"
    by (induct x p rule:ttWF2.induct, auto, (case_tac \<sigma> rule:ttWF.cases, auto)+)
next
  fix x  :: "'a ttobs list"
  show "\<And>P. \<forall>x\<in>P. ttWF x \<Longrightarrow> TT1 P \<Longrightarrow> x \<in> P \<Longrightarrow> \<exists>xa. (\<exists>p\<in>P. xa = (p \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 []) \<or> xa = p \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]) \<and> x \<in> xa"
  proof (induct x rule:ttWF.induct, force, force, force, simp_all)
    fix P :: "'a ttobs list set"
    fix \<sigma> :: "'a ttobs list"
    fix e
    assume ind_hyp: "\<And>P. \<forall>x\<in>P. ttWF x \<Longrightarrow> TT1 P \<Longrightarrow> \<sigma> \<in> P \<Longrightarrow>
      \<exists>xa. (\<exists>p\<in>P. xa = (p \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 []) \<or> xa = p \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]) \<and> \<sigma> \<in> xa"
    assume case_assms: "\<forall>x\<in>P. ttWF x" "TT1 P" "[Event e]\<^sub>E # \<sigma> \<in> P"
    then have "\<forall>x\<in>{t. [Event e]\<^sub>E # t \<in> P}. ttWF x \<and> TT1 {t. [Event e]\<^sub>E # t \<in> P}"
      by (auto simp add: TT1_init_event)
    then have "\<exists>xa. (\<exists>p\<in>{t. [Event e]\<^sub>E # t \<in> P}. xa = (p \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 []) \<or> xa = p \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]) \<and> \<sigma> \<in> xa"
      using case_assms ind_hyp[where P="{t. [Event e]\<^sub>E # t \<in> P}"] by auto
    then show "\<exists>xa. (\<exists>p\<in>P. xa = (p \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 []) \<or> xa = p \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]) \<and> [Event e]\<^sub>E # \<sigma> \<in> xa"
      by force
  next
    fix P :: "'a ttobs list set"
    fix \<sigma> :: "'a ttobs list"
    fix X
    assume ind_hyp: "\<And>P. \<forall>x\<in>P. ttWF x \<Longrightarrow> TT1 P \<Longrightarrow> \<sigma> \<in> P \<Longrightarrow>
      \<exists>xa. (\<exists>p\<in>P. xa = (p \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 []) \<or> xa = p \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]) \<and> \<sigma> \<in> xa"
    assume case_assms: "\<forall>x\<in>P. ttWF x" "TT1 P" "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P"
    then have "\<forall>x\<in>{t. [X]\<^sub>R # [Tock]\<^sub>E # t \<in> P}. ttWF x \<and> TT1 {t. [X]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
      by (auto simp add: TT1_init_tock)
    then have "\<exists>xa. (\<exists>p\<in>{t. [X]\<^sub>R # [Tock]\<^sub>E # t \<in> P}. xa = (p \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 []) \<or> xa = p \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]) \<and> \<sigma> \<in> xa"
      using case_assms ind_hyp[where P="{t. [X]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"] by auto
    then have "\<exists>xa. (\<exists>p\<in>{t. [X]\<^sub>R # [Tock]\<^sub>E # t \<in> P}. xa = p \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]) \<and> \<sigma> \<in> xa"
    proof auto
      fix p
      assume inner_assms: "\<sigma> \<in> p \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 []" "[X]\<^sub>R # [Tock]\<^sub>E # p \<in> P"
      then obtain p' where "p' \<lesssim>\<^sub>C p \<and> \<sigma> \<in> p' \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]"
        using merge_traces2_empty2_prefix_subset_merge_traces2_Tick2 by blast
      then show "\<exists>xa. (\<exists>p. [X]\<^sub>R # [Tock]\<^sub>E # p \<in> P \<and> xa = p \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]) \<and> \<sigma> \<in> xa"
        apply (auto, rule_tac x="p' \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]" in exI, auto)
        apply (rule_tac x="p'" in exI, insert case_assms inner_assms, unfold TT1_def, auto)
        by (meson equalityE tt_prefix_subset.simps(2) tt_prefix_subset.simps(3))
    qed
    then show "\<exists>xa. (\<exists>p\<in>P. xa = (p \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 []) \<or> xa = p \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> xa"
      by force
  next
    fix va and P :: "'a ttobs list set"
    assume "\<forall>x\<in>P. ttWF x" "[Tock]\<^sub>E # va \<in> P"
    then show "\<exists>xa. (\<exists>p\<in>P. xa = (p \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 []) \<or> xa = p \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]) \<and> [Tock]\<^sub>E # va \<in> xa"
      by auto
  next
    fix va and P :: "'a ttobs list set"
    assume "\<forall>x\<in>P. ttWF x" "[Tock]\<^sub>E # va \<in> P"
    then show "\<exists>xa. (\<exists>p\<in>P. xa = (p \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 []) \<or> xa = p \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]) \<and> [Tock]\<^sub>E # va \<in> xa"
      by auto
  next
    fix va and P :: "'a ttobs list set"
    assume "\<forall>x\<in>P. ttWF x" "[Tock]\<^sub>E # va \<in> P"
    then show "\<exists>xa. (\<exists>p\<in>P. xa = (p \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 []) \<or> xa = p \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]) \<and> [Tock]\<^sub>E # va \<in> xa"
      by auto
  next
    fix v vc and P :: "'a ttobs list set"
    assume "\<forall>x\<in>P. ttWF x" "[Tick]\<^sub>E # v # vc \<in> P"
    then show "\<exists>xa. (\<exists>p\<in>P. xa = (p \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 []) \<or> xa = p \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]) \<and> [Tick]\<^sub>E # v # vc \<in> xa"
      by auto
  next
    fix v vc and P :: "'a ttobs list set"
    assume "\<forall>x\<in>P. ttWF x" "[Tick]\<^sub>E # v # vc \<in> P"
    then show "\<exists>xa. (\<exists>p\<in>P. xa = (p \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 []) \<or> xa = p \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]) \<and> [Tick]\<^sub>E # v # vc \<in> xa"
      by auto
  next
    fix va vd vc and P :: "'a ttobs list set"
    assume "\<forall>x\<in>P. ttWF x" "[va]\<^sub>R # [Event vd]\<^sub>E # vc \<in> P"
    then show "\<exists>xa. (\<exists>p\<in>P. xa = (p \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 []) \<or> xa = p \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]) \<and> [va]\<^sub>R # [Event vd]\<^sub>E # vc \<in> xa"
      by auto
  next
    fix va vc and P :: "'a ttobs list set"
    assume "\<forall>x\<in>P. ttWF x" "[va]\<^sub>R # [Tick]\<^sub>E # vc \<in> P"
    then show "\<exists>xa. (\<exists>p\<in>P. xa = (p \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 []) \<or> xa = p \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]) \<and> [va]\<^sub>R # [Tick]\<^sub>E # vc \<in> xa"
      by auto
  next
    fix va v vc and P :: "'a ttobs list set"
    assume "\<forall>x\<in>P. ttWF x" "[va]\<^sub>R # [v]\<^sub>R # vc \<in> P"
    then show "\<exists>xa. (\<exists>p\<in>P. xa = (p \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 []) \<or> xa = p \<lbrakk>{}\<rbrakk>\<^sup>T\<^sub>2 [[Tick]\<^sub>E]) \<and> [va]\<^sub>R # [v]\<^sub>R # vc \<in> xa"
      by auto
  qed
qed

lemma ParComp2_Skip_left_unit:
  assumes "\<forall>x\<in>P. ttWF x" "TT1 P"
  shows "(SKIP\<^sub>C \<lbrakk>{}\<rbrakk>\<^sub>2 P) = P"
  by (simp add: ParComp2_Skip_right_unit ParComp2_comm assms)

lemma ParComp2_Div_right_zero:
  assumes "TT0 P" "TT1 P"
  shows "(P \<lbrakk>UNIV\<rbrakk>\<^sub>2 div\<^sub>C) = div\<^sub>C"
  using assms unfolding ParComp2TT_def DivTT_def
proof auto
  fix x p :: "'a ttobs list"
  show "x \<in> p \<lbrakk>UNIV\<rbrakk>\<^sup>T\<^sub>2 [] \<Longrightarrow> p \<in> P \<Longrightarrow> x = []"
    by (induct x p rule:ttWF2.induct, auto, (case_tac \<sigma> rule:ttWF.cases, auto)+)
next
  assume "TT0 P" "TT1 P"
  then show "\<exists>x. (\<exists>p\<in>P. x = p \<lbrakk>UNIV\<rbrakk>\<^sup>T\<^sub>2 []) \<and> [] \<in> x"
    by (rule_tac x="{[]}" in exI, auto, rule_tac x="[]" in bexI, auto simp add: TT0_TT1_empty)
qed

definition deterministic :: "'a ttobs list set \<Rightarrow> bool" where
  "deterministic P = (\<forall>\<rho> e. (\<exists>X. \<rho> @ [[X]\<^sub>R] \<in> P \<and> e \<in> X) \<longrightarrow>
    ((e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<notin> P) \<or> (\<forall>X. e = Tock \<and> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P)))"

lemma deterministic_ParComp2_idemp:
  assumes "deterministic P" "\<forall>x\<in>P. ttWF x" "TT1 P" "TT2 P" "TT4 P"
  shows "(P \<lbrakk>UNIV\<rbrakk>\<^sub>2 P) = P"
  using assms unfolding ParComp2TT_def
proof auto
  fix p q :: "'a ttobs list"
  show "\<And> P x. deterministic P \<Longrightarrow> TT1 P \<Longrightarrow> TT2 P \<Longrightarrow> TT4 P \<Longrightarrow> x \<in> p \<lbrakk>UNIV\<rbrakk>\<^sup>T\<^sub>2 q \<Longrightarrow> p \<in> P \<Longrightarrow> q \<in> P \<Longrightarrow> x \<in> P"
  proof (induct p q rule:ttWF2.induct, simp_all, safe)
    fix P :: "'a ttobs list set"
    fix X Y x
    assume deterministic_P: "deterministic P" and TT2_P: "TT2 P"
    assume case_assms: "[[X]\<^sub>R] \<in> P" "[[Y]\<^sub>R] \<in> P"
    have  "Y \<inter> {e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {} \<Longrightarrow> [[X \<union> Y]\<^sub>R] \<in> P"
      using TT2_P unfolding TT2_def apply (erule_tac x="[]" in allE, erule_tac x="[]" in allE)
      by (erule_tac x="X" in allE, erule_tac x="Y" in allE, auto simp add: case_assms)
    also have "Y \<inter> {e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
      using deterministic_P unfolding deterministic_def apply (erule_tac x="[]" in allE, auto)
      apply (erule_tac x="x" in allE, auto, erule_tac x="Y" in allE, auto simp add: case_assms)
      by (erule_tac x="Tock" in allE, auto, erule_tac x="Y" in allE, auto simp add: case_assms)
    then show "[[X \<union> Y]\<^sub>R] \<in> P"
      using calculation by auto
  next
    fix P :: "'a ttobs list set"
    fix X A x
    assume deterministic_P: "deterministic P" and TT4_P: "TT4 P"
    assume case_assms: "[[X]\<^sub>R] \<in> P" "[[Tick]\<^sub>E] \<in> P"
    then have "[[X \<union> {Tick}]\<^sub>R] \<in> P"
      using TT4_P unfolding TT4_def by force
    then have False
      using deterministic_P case_assms unfolding deterministic_def by (erule_tac x="[]" in allE, auto)
    then show "[[X \<union> Event ` A]\<^sub>R] \<in> P"
      by auto
  next
    fix P :: "'a ttobs list set"
    fix Y A x
    assume deterministic_P: "deterministic P" and TT4_P: "TT4 P"
    assume case_assms: "[[Y]\<^sub>R] \<in> P" "[[Tick]\<^sub>E] \<in> P"
    then have "[[Y \<union> {Tick}]\<^sub>R] \<in> P"
      using TT4_P unfolding TT4_def by force
    then have False
      using deterministic_P case_assms unfolding deterministic_def by (erule_tac x="[]" in allE, auto)
    then show "[[Y \<union> Event ` A]\<^sub>R] \<in> P"
      by auto
  next
    fix P :: "'a ttobs list set"
    fix Y \<sigma> x W A s
    assume deterministic_P: "deterministic P" and TT1_P: "TT1 P" and TT4_P: "TT4 P"
    assume case_assms: "[[Tick]\<^sub>E] \<in> P" "[Y]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P"
    then have "[[Y]\<^sub>R] \<in> P"
      using TT1_P unfolding TT1_def by force
    then have "[[Y \<union> {Tick}]\<^sub>R] \<in> P"
      using TT4_P unfolding TT4_def by force
    then have False
      using deterministic_P case_assms unfolding deterministic_def by (erule_tac x="[]" in allE, auto)
    then show "[Y \<union> Event ` A]\<^sub>R # [Tock]\<^sub>E # s \<in> P"
      by auto
  next
    fix P :: "'a ttobs list set"
    fix X \<sigma> x W A s
    assume deterministic_P: "deterministic P" and TT1_P: "TT1 P" and TT4_P: "TT4 P"
    assume case_assms: "[[Tick]\<^sub>E] \<in> P" "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P"
    then have "[[X]\<^sub>R] \<in> P"
      using TT1_P unfolding TT1_def by force
    then have "[[X \<union> {Tick}]\<^sub>R] \<in> P"
      using TT4_P unfolding TT4_def by force
    then have False
      using deterministic_P case_assms unfolding deterministic_def by (erule_tac x="[]" in allE, auto)
    then show "[X \<union> Event ` A]\<^sub>R # [Tock]\<^sub>E # s \<in> P"
      by auto
  next
    fix P :: "'a ttobs list set"
    fix \<rho> \<sigma> :: "'a ttobs list"
    fix e f x s
    assume deterministic_P: "deterministic P" and TT1_P: "TT1 P" and TT2_P: "TT2 P" and TT4_P: "TT4 P"
    assume ind_hyp: "\<And>P x. deterministic P \<Longrightarrow> TT1 P \<Longrightarrow> TT2 P \<Longrightarrow> TT4 P \<Longrightarrow> x \<in> \<rho> \<lbrakk>UNIV\<rbrakk>\<^sup>T\<^sub>2 \<sigma> \<Longrightarrow> \<rho> \<in> P \<Longrightarrow> \<sigma> \<in> P \<Longrightarrow> x \<in> P"
    assume case_assms: "[Event f]\<^sub>E # \<rho> \<in> P" "[Event f]\<^sub>E # \<sigma> \<in> P" "s \<in> \<rho> \<lbrakk>UNIV\<rbrakk>\<^sup>T\<^sub>2 \<sigma>"
    have 1: "deterministic {t. [Event f]\<^sub>E # t \<in> P}"
      using deterministic_P unfolding deterministic_def apply auto
      apply (erule_tac x="[Event f]\<^sub>E # \<rho>" in allE, erule_tac x=e in allE, auto)
      apply (erule_tac x="[Event f]\<^sub>E # \<rho>" in allE, erule_tac x=Tock in allE, auto)
      apply (erule_tac x="[Event f]\<^sub>E # \<rho>" in allE, erule_tac x=e in allE, auto)
      done
    have 2: "TT1 {t. [Event f]\<^sub>E # t \<in> P}"
      by (simp add: TT1_P TT1_init_event)
    have 3: "TT2 {t. [Event f]\<^sub>E # t \<in> P}"
      by (simp add: TT2_P TT2_init_event)
    have 4: "TT4 {t. [Event f]\<^sub>E # t \<in> P}"
      by (simp add: TT4_P TT4_init_event)
    show "[Event f]\<^sub>E # s \<in> P"
      using ind_hyp[where P="{t. [Event f]\<^sub>E # t \<in> P}", where x=s] 1 2 3 4 case_assms by auto
  next
    fix P :: "'a ttobs list set"
    fix \<rho> \<sigma> :: "'a ttobs list"
    fix X Y x s
    assume deterministic_P: "deterministic P" and TT1_P: "TT1 P" and TT2_P: "TT2 P" and TT4_P: "TT4 P"
    assume ind_hyp: "\<And>P x. deterministic P \<Longrightarrow> TT1 P \<Longrightarrow> TT2 P \<Longrightarrow> TT4 P \<Longrightarrow> x \<in> \<rho> \<lbrakk>UNIV\<rbrakk>\<^sup>T\<^sub>2 \<sigma> \<Longrightarrow> \<rho> \<in> P \<Longrightarrow> \<sigma> \<in> P \<Longrightarrow> x \<in> P"
    assume case_assms: "[X]\<^sub>R # [Tock]\<^sub>E # \<rho> \<in> P" "[Y]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P" "s \<in> \<rho> \<lbrakk>UNIV\<rbrakk>\<^sup>T\<^sub>2 \<sigma>"
    have 1: "deterministic {t. [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
      using deterministic_P unfolding deterministic_def apply auto
      apply (erule_tac x="[X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<rho>" in allE, erule_tac x=e in allE, auto)
      apply (erule_tac x="[X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<rho>" in allE, erule_tac x=Tock in allE, auto)
      apply (erule_tac x="[X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<rho>" in allE, erule_tac x=e in allE, auto)
      done
    have 2: "TT1 {t. [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
      by (simp add: TT1_P TT1_init_tock)
    have 3: "TT2 {t. [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
      by (simp add: TT2_P TT2_init_tock)
    have 4: "TT4 {t. [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
      by (simp add: TT1_P TT4_P TT4_TT1_init_tock)
    have "Y \<inter> {e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
      using deterministic_P unfolding deterministic_def apply auto
      apply (erule_tac x="[]" in allE, erule_tac x="x" in allE, auto, erule_tac x="Y" in allE, auto)
      apply (meson TT1_P TT1_def case_assms(2) equalityE tt_prefix_subset.simps(1) tt_prefix_subset.simps(2))
      apply (erule_tac x="[]" in allE, erule_tac x="Tock" in allE, auto, erule_tac x="Y" in allE, auto)
      apply (meson TT1_P TT1_def case_assms(2) equalityE tt_prefix_subset.simps(1) tt_prefix_subset.simps(2))
      done
    then have 5: "[X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<rho> \<in> P"
      using TT2_P unfolding TT2_def apply (erule_tac x="[]" in allE, erule_tac x="[Tock]\<^sub>E # \<rho>" in allE)
      by (erule_tac x="X" in allE, erule_tac x="Y" in allE, auto simp add: case_assms)
    have "X \<inter> {e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> [[Y]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
      using deterministic_P unfolding deterministic_def apply auto
      apply (erule_tac x="[]" in allE, erule_tac x="x" in allE, auto, erule_tac x="X" in allE, auto)
      apply (meson TT1_P TT1_def case_assms(1) equalityE tt_prefix_subset.simps(1) tt_prefix_subset.simps(2))
      apply (erule_tac x="[]" in allE, erule_tac x="Tock" in allE, auto, erule_tac x="X" in allE, auto)
      apply (meson TT1_P TT1_def case_assms(1) equalityE tt_prefix_subset.simps(1) tt_prefix_subset.simps(2))
      done
    then have 6: "[X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P"
      using TT2_P unfolding TT2_def apply (erule_tac x="[]" in allE, erule_tac x="[Tock]\<^sub>E # \<sigma>" in allE)
      by (erule_tac x="Y" in allE, erule_tac x="X" in allE, auto simp add: case_assms Un_commute)
    show "[X \<union> Y]\<^sub>R # [Tock]\<^sub>E # s \<in> P"
      using ind_hyp[where P="{t. [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # t \<in> P}", where x=s] 1 2 3 4 5 6 case_assms by auto
  qed
next
  fix x :: "'a ttobs list"
  show "\<And>P. \<forall>x\<in>P. ttWF x \<Longrightarrow> x \<in> P \<Longrightarrow> \<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>P. xa = p \<lbrakk>UNIV\<rbrakk>\<^sup>T\<^sub>2 q) \<and> x \<in> xa"
  proof (induct x rule:ttWF.induct, auto)
    fix P :: "'a ttobs list set"
    show "[] \<in> P \<Longrightarrow> \<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>P. xa = p \<lbrakk>UNIV\<rbrakk>\<^sup>T\<^sub>2 q) \<and> [] \<in> xa"
      by (rule_tac x="{[]}" in exI, auto, rule_tac x="[]" in bexI, rule_tac x="[]" in bexI, auto)
  next
    fix P :: "'a ttobs list set"
    fix X
    show "[[X]\<^sub>R] \<in> P \<Longrightarrow> \<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>P. xa = p \<lbrakk>UNIV\<rbrakk>\<^sup>T\<^sub>2 q) \<and> [[X]\<^sub>R] \<in> xa"
      by (rule_tac x="[[X]\<^sub>R] \<lbrakk>UNIV\<rbrakk>\<^sup>T\<^sub>2 [[X]\<^sub>R]" in exI, auto, rule_tac x="[[X]\<^sub>R]" in bexI, rule_tac x="[[X]\<^sub>R]" in bexI, auto)
  next
    fix P :: "'a ttobs list set"
    show "[[Tick]\<^sub>E] \<in> P \<Longrightarrow> \<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>P. xa = p \<lbrakk>UNIV\<rbrakk>\<^sup>T\<^sub>2 q) \<and> [[Tick]\<^sub>E] \<in> xa"
      by (rule_tac x="{[[Tick]\<^sub>E]}" in exI, auto, rule_tac x="[[Tick]\<^sub>E]" in bexI, rule_tac x="[[Tick]\<^sub>E]" in bexI, auto)
  next
    fix P :: "'a ttobs list set"
    fix \<sigma> :: "'a ttobs list"
    fix e
    assume P_wf: "\<forall>x\<in>P. ttWF x"
    assume ind_hyp: "\<And>P. \<forall>x\<in>P. ttWF x \<Longrightarrow> \<sigma> \<in> P \<Longrightarrow> \<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>P. xa = p \<lbrakk>UNIV\<rbrakk>\<^sup>T\<^sub>2 q) \<and> \<sigma> \<in> xa"
    assume case_assms: "[Event e]\<^sub>E # \<sigma> \<in> P"
    have "\<forall>x\<in>{t. [Event e]\<^sub>E # t \<in> P}. ttWF x"
      using P_wf by auto
    then have "\<exists>xa. (\<exists>p. [Event e]\<^sub>E # p \<in> P \<and> (\<exists>q. [Event e]\<^sub>E # q \<in> P \<and> xa = p \<lbrakk>UNIV\<rbrakk>\<^sup>T\<^sub>2 q)) \<and> \<sigma> \<in> xa"
      using ind_hyp[where P="{t. [Event e]\<^sub>E # t \<in> P}"] P_wf case_assms by auto
    then obtain p q where "[Event e]\<^sub>E # p \<in> P \<and> [Event e]\<^sub>E # q \<in> P \<and> \<sigma> \<in> p \<lbrakk>UNIV\<rbrakk>\<^sup>T\<^sub>2 q"
      by auto
    then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>P. xa = p \<lbrakk>UNIV\<rbrakk>\<^sup>T\<^sub>2 q) \<and> [Event e]\<^sub>E # \<sigma> \<in> xa"
      apply (rule_tac x="[Event e]\<^sub>E # p \<lbrakk>UNIV\<rbrakk>\<^sup>T\<^sub>2 [Event e]\<^sub>E # q" in exI, auto)
      by (rule_tac x="[Event e]\<^sub>E # p" in bexI, rule_tac x="[Event e]\<^sub>E # q" in bexI, auto)
  next
    fix P :: "'a ttobs list set"
    fix \<sigma> :: "'a ttobs list"
    fix X
    assume P_wf: "\<forall>x\<in>P. ttWF x"
    assume ind_hyp: "\<And>P. \<forall>x\<in>P. ttWF x \<Longrightarrow> \<sigma> \<in> P \<Longrightarrow> \<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>P. xa = p \<lbrakk>UNIV\<rbrakk>\<^sup>T\<^sub>2 q) \<and> \<sigma> \<in> xa"
    assume case_assms: "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P"
    have "\<forall>x\<in>{t. [X]\<^sub>R # [Tock]\<^sub>E # t \<in> P}. ttWF x"
      using P_wf by auto
    then have "\<exists>xa. (\<exists>p\<in>{t. [X]\<^sub>R # [Tock]\<^sub>E # t \<in> P}. \<exists>q\<in>{t. [X]\<^sub>R # [Tock]\<^sub>E # t \<in> P}. xa = p \<lbrakk>UNIV\<rbrakk>\<^sup>T\<^sub>2 q) \<and> \<sigma> \<in> xa"
      using ind_hyp[where P="{t. [X]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"] P_wf case_assms by auto
    then obtain p q where "[X]\<^sub>R # [Tock]\<^sub>E # p \<in> P \<and> [X]\<^sub>R # [Tock]\<^sub>E # q \<in> P \<and> \<sigma> \<in> p \<lbrakk>UNIV\<rbrakk>\<^sup>T\<^sub>2 q"
      by auto
    then show "\<exists>xa. (\<exists>p\<in>P. \<exists>q\<in>P. xa = p \<lbrakk>UNIV\<rbrakk>\<^sup>T\<^sub>2 q) \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> xa"
      apply (rule_tac x="[X]\<^sub>R # [Tock]\<^sub>E # p \<lbrakk>UNIV\<rbrakk>\<^sup>T\<^sub>2 [X]\<^sub>R # [Tock]\<^sub>E # q" in exI, auto)
      by (rule_tac x="[X]\<^sub>R # [Tock]\<^sub>E # p" in bexI, rule_tac x="[X]\<^sub>R # [Tock]\<^sub>E # q" in bexI, auto)
  qed
qed

end