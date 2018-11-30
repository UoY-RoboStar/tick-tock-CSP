theory CTockTick_Hiding
  imports CTockTick_Core
begin

subsection {* Hiding *}

fun hide_trace :: "'a cttevent set \<Rightarrow> 'a cttobs list \<Rightarrow> 'a cttobs list set" where
  "hide_trace X [] = {[]}" |
  "hide_trace X ([Event e]\<^sub>E # s) =
    {t. (Event e \<in> X \<and> t \<in> hide_trace X s) \<or> (\<exists>s'. Event e \<notin> X \<and> s' \<in> hide_trace X s \<and> t = [Event e]\<^sub>E # s')}" |
  "hide_trace X ([Tick]\<^sub>E # s) =
    {t. (Tick \<in> X \<and> t \<in> hide_trace X s) \<or> (\<exists>s'. Tick \<notin> X \<and> s \<in> hide_trace X s \<and> t = [Tick]\<^sub>E # s')}" |
  "hide_trace X ([Y]\<^sub>R # [Tock]\<^sub>E # s) =
    {t. (Tock \<in> X \<and> t \<in> hide_trace X s) \<or> (\<exists> s'. \<exists> Z\<subseteq>X. Tock \<notin> X \<and> t = [Y \<union> Z]\<^sub>R # [Tock]\<^sub>E # s' \<and> s' \<in> hide_trace X s)}" |
  "hide_trace X [[Y]\<^sub>R] = {t. \<exists> Z\<subseteq>X. t = [[Y \<union> Z]\<^sub>R]}" |
  "hide_trace X ([Tock]\<^sub>E # t) = {}" |
  "hide_trace X ([Y]\<^sub>R # [Event e]\<^sub>E # t) = {}" |
  "hide_trace X ([Y]\<^sub>R # [Tick]\<^sub>E # t) = {}" |
  "hide_trace X ([Y]\<^sub>R # [Z]\<^sub>R # t) = {}"

definition HidingCTT :: "'a cttobs list set \<Rightarrow> 'a cttevent set \<Rightarrow> 'a cttobs list set" (infixl "\<setminus>\<^sub>C" 53) where
  "HidingCTT P X = \<Union> {hide_trace X p | p. p \<in> P}"

