theory CTock
imports 
  Main
  "HOL-Library.Sublist"
  List
begin

section \<open> Base sequence type \<close>

datatype 'a tockevent = Event 'a | tock
datatype 'a revent = Ref "'a set" | REvent 'a

instantiation tockevent :: (type) order
begin

definition less_eq_tockevent :: "'a tockevent \<Rightarrow> 'a tockevent \<Rightarrow> bool" where
"less_eq_tockevent a b = (a = b)"

definition less_tockevent :: "'a tockevent \<Rightarrow> 'a tockevent \<Rightarrow> bool" where
"less_tockevent a b = (a \<le> b \<and> \<not>b \<le> a)"

instance
  apply intro_classes
  by (auto simp add:less_eq_tockevent_def less_tockevent_def)
end

instantiation revent :: (type) order
begin

fun less_eq_revent :: "'a revent \<Rightarrow> 'a revent \<Rightarrow> bool" where
"less_eq_revent (Ref a) (Ref b) = (a \<subseteq> b)" |
"less_eq_revent (REvent a) (REvent b) = (a = b)" |
"less_eq_revent a b = False"

definition less_revent :: "'a revent \<Rightarrow> 'a revent \<Rightarrow> bool" where
"less_revent a b = (a \<le> b \<and> \<not>b \<le> a)"

lemma revent_refl:
  fixes x :: "'a revent"
  shows "x \<le> x"
  by (induct x, auto)

lemma revent_trans:
  fixes x y z :: "'a revent"
  shows "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
  apply (induct x z arbitrary:y rule:less_eq_revent.induct)
    apply (simp_all)
     apply auto
  by (case_tac y, auto)+

lemma revent_antisym:
  fixes x y z :: "'a revent"
  shows "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
  apply (induct x y rule:less_eq_revent.induct)
  by auto

instance
  apply (intro_classes)
     apply (auto simp add:less_revent_def revent_refl)
   apply (auto simp add:revent_antisym)
  using revent_trans by blast
end

type_synonym 'a ctocke = "(('a tockevent) revent)"
type_synonym 'a ctockl = "'a ctocke list"
type_synonym 'a ctocks = "'a ctockl set"

text \<open> A CTock trace is a well-defined sequence according to the 
       following function \<close>

fun ctockWD :: "'a ctockl \<Rightarrow> bool" where
"ctockWD [] = True" |
(* initially this was ctockWD (REvent (Event a) # va), but note that
   even before a 'tock' the refusals are optional. In the case, for
   example, of div [] tock \<rightarrow> P, we have no initial refusal observation,
   but tock can still nevertheless happen *)
"ctockWD (REvent a # va) = (ctockWD va)" |
"ctockWD (Ref r # []) = True" |
"ctockWD (Ref r # (REvent tock) # v) = (tock \<notin> r \<and> ctockWD v)" |
"ctockWD X = False"

text \<open> Prefixing for a CTock trace is defined by CTock_less_le. \<close>

fun CTock_less_le :: "'a ctockl \<Rightarrow> 'a ctockl \<Rightarrow> bool" where
"CTock_less_le [] xs = True" |
"CTock_less_le (a # xs) (b # ys) = (a \<le> b \<and> CTock_less_le xs ys)" |
"CTock_less_le (x # xs) [] = False"

fun list_le :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
"list_le [] a = True" |
"list_le (x # xs) (y # ys) = (x = y \<and> list_le xs ys)" |
"list_le (x # xs) [] = False"

lemma list_le_concat_prefix:
  "prefix xs (xs @ y)"
  by (induct xs, auto)

lemma list_le_concat_prefix_also_prefix:
  assumes "prefix (xs@ys) z"
  shows "prefix xs z"
  using assms Sublist.append_prefixD by (auto)

fun ctockl_tl :: "'a ctockl \<Rightarrow> 'a ctockl" where
"ctockl_tl (REvent (Event a) # va) = va" |
"ctockl_tl (Ref r # (REvent tock) # v) = v" |
"ctockl_tl X = []"

(*
fun ctockl_append :: "'a ctockl \<Rightarrow> 'a ctockl \<Rightarrow> 'a ctockl" (infix "@\<^sub>C" 65) where
"ctockl_append [] b = b" |
"ctockl_append b [] = b" |
"ctockl_append (Ref r # (REvent tock) # v) x = (Ref r # (REvent tock) # ctockl_append v x)" |
"ctockl_append [Ref r] (REvent tock # x) = (if tock \<notin> r then (Ref r # (REvent tock) # x) else [Ref r])" |
"ctockl_append [Ref r] (REvent a # x) = ctockl_append [Ref r] x" |
"ctockl_append [Ref r] [Ref s] = [Ref s]" |
"ctockl_append [Ref r] (Ref s # REvent tock # x) = (if tock \<notin> r then (Ref r # REvent tock # x) else [])" |
"ctockl_append (Ref r # v) (Ref s # x) = (ctockl_append v (Ref s # x))" |
"ctockl_append (REvent a # va) x = (REvent a # ctockl_append va x)" |
"ctockl_append x y = []"
*)


fun ctockl_append :: "'a ctockl \<Rightarrow> 'a ctockl \<Rightarrow> 'a ctockl" (infix "@\<^sub>C" 65) where
"ctockl_append [] b = b" |
"ctockl_append b [] = b" |
"ctockl_append (Ref r # (REvent tock) # v) x = (Ref r # (REvent tock) # ctockl_append v x)" |
"ctockl_append [Ref r] (REvent tock # x) = (if tock \<notin> r then (Ref r # (REvent tock) # x) else (REvent tock # x))" |
"ctockl_append [Ref r] (REvent a # x) = (REvent a # x)" |
"ctockl_append [Ref r] [Ref s] = [Ref s]" |
"ctockl_append [Ref r] (Ref s # REvent tock # x) = (Ref s # REvent tock # x)" |
"ctockl_append (Ref r # v) (s # x) = (ctockl_append v (s # x))" |
"ctockl_append (REvent a # va) x = (REvent a # ctockl_append va x)"


lemma ctockl_append_is_ctockWD:
  assumes "ctockWD s" "ctockWD t"
  shows "ctockWD (ctockl_append s t)"
  using assms by (induct s t rule:ctockl_append.induct, auto)

section \<open> Proper type ctock \<close>

typedef 'a ctock = "{x::'a ctockl. ctockWD x}" 
  by (rule exI[where x="[]"], auto)

setup_lifting type_definition_ctock

lift_definition chd :: "'a ctock \<Rightarrow> 'a ctocke" is hd .
lift_definition cecons :: "'a \<Rightarrow> 'a ctock \<Rightarrow> 'a ctock" (infix "#\<^sub>C\<^sub>e" 65) is 
  "\<lambda>e y. (REvent (Event e) # y)" by auto
lift_definition ctcons :: "'a set \<Rightarrow> 'a ctock \<Rightarrow> 'a ctock" (infix "#\<^sub>C\<^sub>t" 65) is 
  "\<lambda>r y. (Ref {Event e| e. e \<in>r} # (REvent tock) # y)" by auto
lift_definition cappend :: "'a ctock \<Rightarrow> 'a ctock \<Rightarrow> 'a ctock" (infix "@\<^sub>C\<^sub>t" 65) is 
  ctockl_append by (auto simp add:ctockl_append_is_ctockWD)
lift_definition cstdprefix :: "'a ctock \<Rightarrow> 'a ctock \<Rightarrow> bool" (infix "\<le>\<^sub>C\<^sub>t" 65) is 
  prefix .

instantiation ctock :: (type) order
begin

lift_definition less_eq_ctock :: "'a ctock \<Rightarrow> 'a ctock \<Rightarrow> bool" is CTock_less_le .

definition less_ctock :: "'a ctock \<Rightarrow> 'a ctock \<Rightarrow> bool" where
"less_ctock a b = (a \<le> b \<and> \<not>b \<le> a)"

lemma CTock_less_le_rel:
  fixes x :: "'a ctockl"
  shows "CTock_less_le x x" 
  by (induct x, auto)

lemma ctock_refl:
  fixes x :: "'a ctock"
  shows "x \<le> x" 
  apply transfer
  by (auto simp add:CTock_less_le_rel)

lemma CTock_less_le_trans:
  fixes x y z :: "'a ctockl"
  shows "CTock_less_le x y \<Longrightarrow> CTock_less_le y z \<Longrightarrow> CTock_less_le x z"
  apply (induct x z arbitrary:y rule:CTock_less_le.induct)
    apply (simp_all)
  by (case_tac y, auto)+

lemma ctock_trans:
  fixes x :: "'a ctock"
  shows "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" 
  apply transfer
  using CTock_less_le_trans by blast

lemma CTock_less_le_antisym:
  fixes x y z :: "'a ctockl"
  shows "CTock_less_le x y \<Longrightarrow> CTock_less_le y x \<Longrightarrow> x = y"
  apply (induct x y rule:CTock_less_le.induct, auto)
  by (case_tac xs, auto)

lemma ctock_antisym:
  fixes x y z :: "'a ctock"
  shows "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
  apply transfer
  using CTock_less_le_antisym by blast

instance 
  apply intro_classes
     apply (auto simp add:less_ctock_def ctock_refl ctock_antisym)
  using ctock_trans by blast
end

section \<open> Healthiness conditions \<close>

definition CTock0 :: "'a ctock set \<Rightarrow> bool" where
"CTock0 P \<equiv> P \<noteq> {}"

definition CTockl0 :: "'a ctockl set \<Rightarrow> bool" where
"CTockl0 P \<equiv> P \<noteq> {}"

definition CTock1 :: "'a ctock set \<Rightarrow> bool" where
"CTock1 P \<equiv> (\<forall>s t. t \<in> P \<and> s \<le> t \<longrightarrow> s \<in> P)"

definition CTock2 :: "'a ctock set \<Rightarrow> bool" where
"CTock2 P \<equiv> (\<forall>s t. t \<in> P \<and> s \<le>\<^sub>C\<^sub>t t \<longrightarrow> s \<in> P)"

definition CTockl1 :: "'a ctockl set \<Rightarrow> bool" where
"CTockl1 P \<equiv> (\<forall>s t. t \<in> P \<and> CTock_less_le s t \<longrightarrow> s \<in> P)"

definition CTockl1_WD :: "'a ctockl set \<Rightarrow> bool" where
"CTockl1_WD P \<equiv> (\<forall>s t. t \<in> P \<and> ctockWD s \<and> CTock_less_le s t \<longrightarrow> s \<in> P)"

definition CTockl2_WD :: "'a ctockl set \<Rightarrow> bool" where
"CTockl2_WD P \<equiv> (\<forall>s t. t \<in> P \<and> ctockWD s \<and> prefix s t \<longrightarrow> s \<in> P)"

definition CTockl2 :: "'a ctockl set \<Rightarrow> bool" where
"CTockl2 P \<equiv> (\<forall>s t. t \<in> P \<and> prefix s t \<longrightarrow> s \<in> P)"

text \<open> If a tock follows a refusal, then it is also the case that there could
       have been no refusal. It is somewhat disappointing that we cannot capture
       this as part of the prefix relation. \<close>

definition CTockl3 :: "'a ctockl set \<Rightarrow> bool" where
"CTockl3 P \<equiv> (\<forall>s X. s @ [Ref X, REvent tock] \<in> P \<longrightarrow> s @ [REvent tock] \<in> P)"

lemma CTock2_iff_CTockl2_WD:
  "CTock2 P = CTockl2_WD({Rep_ctock x|x. x \<in> P})"
  unfolding CTock2_def CTockl2_WD_def apply transfer
  by auto

lemma ctockWD_list_le:
  assumes "ctockWD t" "prefix s t"
  shows "ctockWD s"
  using assms apply (induct s arbitrary: t rule:ctockWD.induct, auto) 
  apply (metis append_Cons ctockWD.simps(2) list_le_concat_prefix prefixE)
     apply (metis (mono_tags, lifting) append_Cons ctockWD.simps(4) prefix_def)
    apply (smt Cons_prefix_Cons ctockWD.elims(2) prefix_code(2) revent.distinct(1))
  apply (smt Cons_prefix_Cons ctockWD.elims(2) prefix_code(2) revent.distinct(1))
  by (smt Cons_prefix_Cons ctockWD.elims(2) prefix_code(2) revent.distinct(1) revent.inject(2) tockevent.distinct(1))
 
lemma ctockWD_CTock_less_le:
  assumes "ctockWD t" "CTock_less_le s t"
  shows "ctockWD s"
  using assms apply (induct s t rule:CTock_less_le.induct, auto)
  apply (case_tac a, auto)
  apply (case_tac b, auto)
  apply (smt CTock_less_le.elims(2) ctockWD.elims(2) ctockWD.simps(2) ctockWD.simps(3) ctockWD.simps(4) less_eq_revent.elims(2) list.distinct(1) list.sel(1) list.sel(3) revent.distinct(1) subsetCE)
  by (case_tac b, auto)

lemma CTockl1_WD_imp_CTockl1:
  assumes "CTockl1_WD P" "\<forall>x\<in>P. ctockWD x"
  shows "CTockl1 P"
  using assms unfolding CTockl1_def CTockl1_WD_def
  using ctockWD_CTock_less_le by blast

lemma CTockl2_WD_imp_CTockl2:
  assumes "CTockl2_WD P" "\<forall>x\<in>P. ctockWD x"
  shows "CTockl2 P"
  using assms unfolding CTockl2_def CTockl2_WD_def
  using ctockWD_list_le
  by blast

lemma CTock2_iff_CTockl2:
  "CTock2 P = CTockl2({Rep_ctock x|x. x \<in> P})"
  unfolding CTock2_def CTockl2_WD_def apply transfer
  by (smt CTockl2_def ctockWD_list_le mem_Collect_eq)

lemma CTock1_iff_CTockl1_WD:
  "CTock1 P = CTockl1_WD({Rep_ctock x|x. x \<in> P})"
  unfolding CTock1_def CTockl1_WD_def apply transfer
  by auto

lemma CTock2_iff_CTockl1:
  "CTock1 P = CTockl1({Rep_ctock x|x. x \<in> P})"
  unfolding CTock1_def CTockl1_WD_def apply transfer
  by (smt CTockl1_def ctockWD_CTock_less_le mem_Collect_eq)

lemma list_le_imp_CTock_less_le:
  assumes "prefix s t"
  shows "CTock_less_le s t"
  using assms by (induct s t rule:list_le.induct, auto)

lemma CTock_less_le_imp_less_le:
  "\<forall>s. (\<exists>t. t \<in> P \<and> CTock_less_le s t) \<longrightarrow> s \<in> P \<Longrightarrow> t \<in> P \<Longrightarrow> prefix s t \<Longrightarrow> s \<in> P"
  apply (induct s t rule:list_le.induct, auto)
  using CTock_less_le.simps(1) apply blast
  using CTock_less_le.simps(2) list_le_imp_CTock_less_le by blast

lemma CTockl1_imp_CTockl2: "CTockl1 P \<longrightarrow> CTockl2 P"
  unfolding CTockl1_def CTockl2_def apply auto
  using list_le_imp_CTock_less_le by blast

lemma CT0s_CT1s_imp_nil:
  assumes "CTock0 P" "CTock1 P"
  shows "Abs_ctock [] \<in> P"
  using assms unfolding CTock0_def CTock1_def
  apply auto
  by (metis Abs_ctock_inverse CTock_less_le.simps(1) ctockWD.simps(1) less_eq_ctock.rep_eq mem_Collect_eq)

lemma CT0s_CT2s_imp_nil:
  assumes "CTock0 P" "CTock2 P"
  shows "Abs_ctock [] \<in> P"
  using assms unfolding CTock0_def CTock2_def
  apply auto
  by (metis Abs_ctock_inverse cstdprefix.rep_eq ctockWD.simps(1) mem_Collect_eq prefix_bot.bot.extremum)
  
lemma CTl0s_CTl2s_imp_nil:
  assumes "CTockl0 P" "CTockl2 P"
  shows "[] \<in> P"
  using assms unfolding CTockl0_def CTockl2_def
  apply auto
  by (metis Abs_ctock_inverse cstdprefix.rep_eq ctockWD.simps(1) mem_Collect_eq prefix_bot.bot.extremum)
  
text \<open>Easier to use the following lifted definitions when using the transfer method.\<close>

lift_definition xCTock1 :: "'a ctock set \<Rightarrow> bool" is CTockl1 .
lift_definition xCTock2 :: "'a ctock set \<Rightarrow> bool" is CTockl2 .

lemma xCTock1_imp_xCTock2:
  assumes "xCTock1 P"
  shows "xCTock2 P"
  using assms apply transfer
  by (simp add: CTockl1_imp_CTockl2)

definition mkCTockl1 :: "'a ctockl set \<Rightarrow> 'a ctockl set" where
"mkCTockl1 P \<equiv> P \<union> {s. \<exists>z. z \<in> P \<and> CTock_less_le s z}"

lemma mkCTockl1_iff_CTockl1:
  "mkCTockl1 P = P \<longleftrightarrow> CTockl1 P"
  unfolding mkCTockl1_def CTockl1_def by auto

lemma mkCTockl1_mono:
  assumes "P \<subseteq> Q"
  shows "mkCTockl1(P) \<subseteq> mkCTockl1(Q)"
  using assms unfolding mkCTockl1_def by auto

lemma mkCTockl1_univ_disj:
  "mkCTockl1 (\<Union> P) = \<Union>{mkCTockl1 x|x. x \<in> P}"
  unfolding mkCTockl1_def by auto

definition unmkCTockl1 :: "'a ctockl set \<Rightarrow> 'a ctockl set" where
"unmkCTockl1 P = \<Union>{s. (mkCTockl1(s) \<subseteq> P)}"

lemma unmkCTockl1_mono:
  assumes "P \<subseteq> Q"
  shows "unmkCTockl1(P) \<subseteq> unmkCTockl1(Q)"
  using assms unfolding unmkCTockl1_def by auto

lemma mkCTockl1_unmkCTockl1_sub:
  shows "mkCTockl1(unmkCTockl1(P)) \<subseteq> P"
  unfolding mkCTockl1_def unmkCTockl1_def by auto

lemma sub_mkCTockl1_unmkCTockl1:
  assumes "P = mkCTockl1(P)"
  shows "P \<subseteq> mkCTockl1(unmkCTockl1(P))"
proof -
  have "(P \<subseteq> mkCTockl1(unmkCTockl1(P)))
        =
        (P \<subseteq> mkCTockl1(unmkCTockl1(mkCTockl1(P))))"
    using assms by auto
  also have "... = True"
    unfolding mkCTockl1_def unmkCTockl1_def by auto
  finally show ?thesis by auto
qed

lemma mkCTockl1_unmkCTockl1_bij:
  assumes "CTockl1 P"
  shows "P = mkCTockl1(unmkCTockl1(P))"
  using assms
  by (metis  dual_order.antisym mkCTockl1_iff_CTockl1 mkCTockl1_unmkCTockl1_sub sub_mkCTockl1_unmkCTockl1)

lemma mkCTockl1_is_CTockl2:
  shows "CTockl2(mkCTockl1(P))"
  by (smt CTock_less_le_trans CTockl2_def UnCI UnE list_le_imp_CTock_less_le mem_Collect_eq mkCTockl1_def)

definition mkCTockl2 :: "'a ctockl set \<Rightarrow> 'a ctockl set" where
"mkCTockl2 P \<equiv> P \<union> {s. \<exists>z. z \<in> P \<and> prefix s z}"

lemma mkCTockl2_iff_CTockl2:
  "mkCTockl2 P = P \<longleftrightarrow> CTockl2 P"
  unfolding mkCTockl2_def CTockl2_def by auto

end