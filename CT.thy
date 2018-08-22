
theory CT
imports
  Main
  CTock
  List
begin

datatype 'a tevent = Tock "'a set" | Event 'a

instantiation tevent :: (type) order
begin

fun less_eq_tevent :: "'a tevent \<Rightarrow> 'a tevent \<Rightarrow> bool" where
"less_eq_tevent (Tock a) (Tock b) = (a \<subseteq> b)" |
"less_eq_tevent (Event a) (Event b) = (a = b)" |
"less_eq_tevent x y = False"

definition less_tevent :: "'a tevent \<Rightarrow> 'a tevent \<Rightarrow> bool" where
"less_tevent a b = (a \<le> b \<and> \<not> b \<le> a)"

lemma tevent_refl:
  fixes x :: "'a tevent"
  shows "x \<le> x"
  apply (cases x)
  by auto

lemma tevent_trans:
  fixes x y z :: "'a tevent"
  shows "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
  apply (cases y, auto)
   apply (cases x, auto)
  by (cases z, auto)+

lemma tevent_antisym:
  fixes x y z :: "'a tevent"
  shows "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
  apply (cases y, auto)
  by (cases x, auto)+

instance 
  apply intro_classes
  apply (simp add:less_tevent_def)
  using tevent_refl apply auto
  using tevent_trans apply blast
  by (auto simp add:  tevent_antisym)
end

datatype 'a listle = LNil ("\<langle>\<rangle>\<^sub>L") |
                     LCons 'a "'a listle" (infix "#\<^sub>L" 65)

instantiation listle :: (order) order
begin

fun less_eq_listle :: "'a listle \<Rightarrow> 'a listle \<Rightarrow> bool" where
"less_eq_listle LNil b = True" |
"less_eq_listle (a #\<^sub>L xa) (b #\<^sub>L xb) = (a \<le> b \<and> less_eq_listle xa xb)" |
"less_eq_listle xa xb = False"

definition less_listle :: "'a listle \<Rightarrow> 'a listle \<Rightarrow> bool" where
"less_listle a b = (a \<le> b \<and> \<not>b \<le> a)"

lemma listle_refl:
  fixes x :: "'a listle"
  shows "x \<le> x"
  apply (induct x rule:listle.induct)
  by auto

lemma listle_trans:
  fixes x y z :: "'a listle"
  shows "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
  apply (induct x z arbitrary:y rule:less_eq_listle.induct)
    apply (simp_all)
  apply auto
  apply (metis CT.less_eq_listle.simps(2) dual_order.trans less_eq_listle.elims(2))
   apply (metis CT.less_eq_listle.simps(2) dual_order.trans less_eq_listle.elims(2))
  by (case_tac y, auto)

lemma listle_antisym:
  fixes x y z :: "'a listle"
  shows "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
  apply (induct x y rule:less_eq_listle.induct)
  apply auto
  by (case_tac b, auto)

instance
  apply intro_classes
     apply (simp_all add:less_listle_def)
    apply (simp add:listle_refl)
  using listle_trans apply blast
  using listle_antisym by auto
end

syntax
  "_listle"     :: "args \<Rightarrow> 'e listle"    ("\<langle>(_)\<rangle>\<^sub>L")

translations
  "\<langle>x, xs\<rangle>\<^sub>L" == "(x #\<^sub>L \<langle>xs\<rangle>\<^sub>L)"
  "\<langle>x\<rangle>\<^sub>L" == "x #\<^sub>L \<langle>\<rangle>\<^sub>L"
                   
primrec listle2list :: "'a listle \<Rightarrow> 'a list" where
"listle2list LNil = []" |
"listle2list (LCons S xs) = S # listle2list xs"

primrec list2listle :: "'a list \<Rightarrow> 'a listle" where
"list2listle [] = LNil" |
"list2listle (Cons S xs) = (LCons S (list2listle xs))"

lemma ct2list: "listle2list(list2listle s) = s"
  by (induct s, auto)
  
lemma list2ct: "list2listle(listle2list s) = s"
  by (induct s, auto)

datatype 'a ctrace = 
  CNil  ("\<langle>\<rangle>\<^sub>C") |
  CRef  "'a set" ("[_]\<^sub>C") |
  CTock "'a set" "'a ctrace" (infix "#\<^sub>C\<^sub>T" 65) |
  CCons 'a "'a ctrace" (infix "#\<^sub>C\<^sub>E" 65)

syntax
  "_cevents"    :: "args  \<Rightarrow> 'e ctrace"    ("\<langle>(_)\<rangle>\<^sub>C")
  "_ctock"      :: "'e  \<Rightarrow> 'e set"         ("[_]\<^sub>T")
  "_cref"       :: "'e  \<Rightarrow> 'e set"         ("[_]\<^sub>R")
  
translations
  "\<langle>[x]\<^sub>R\<rangle>\<^sub>C" == "[x]\<^sub>C"
  "\<langle>[x]\<^sub>T,xs\<rangle>\<^sub>C" == "(x #\<^sub>C\<^sub>T \<langle>xs\<rangle>\<^sub>C)"
  "\<langle>x,xs\<rangle>\<^sub>C" == "(x #\<^sub>C\<^sub>E \<langle>xs\<rangle>\<^sub>C)"
  "\<langle>[x]\<^sub>T\<rangle>\<^sub>C" == "(x #\<^sub>C\<^sub>T \<langle>\<rangle>\<^sub>C)"
  "\<langle>x\<rangle>\<^sub>C" == "(x #\<^sub>C\<^sub>E \<langle>\<rangle>\<^sub>C)"

term "\<langle>x, x, d\<rangle>\<^sub>C"
term "[{1}]\<^sub>C"
term "\<langle>[{1}]\<^sub>R\<rangle>\<^sub>C"
term "\<langle>[{1}]\<^sub>T\<rangle>\<^sub>C"
term "\<langle>e,[x]\<^sub>R\<rangle>\<^sub>C"

instantiation ctrace :: (type) order 
begin

fun less_eq_ctrace :: "'a ctrace \<Rightarrow> 'a ctrace \<Rightarrow> bool" where
-- \<open> Empty trace is always a prefix. \<close>
  "less_eq_ctrace \<langle>\<rangle>\<^sub>C s = True"
-- \<open> A non-timed refusal set must be a subset. \<close>
| "less_eq_ctrace [X]\<^sub>C [Y]\<^sub>C = (X \<subseteq> Y)"
-- \<open> A timed refusal is prefixed by an untimed refusal. \<close>
| "less_eq_ctrace [X]\<^sub>C (Y #\<^sub>C\<^sub>T ys) = (X \<subseteq> Y)"
-- \<open> A untimed refusal can be followed by any sequence of events. \<close>
(*| "less_eq_ctrace [X]\<^sub>C (e #\<^sub>C\<^sub>E ys) = True"*)
-- \<open> Timed refusals are compared. \<close>
| "less_eq_ctrace (X #\<^sub>C\<^sub>T xs) (Y #\<^sub>C\<^sub>T ys) = (X \<subseteq> Y \<and> xs \<le> ys)"
-- \<open> Events must be the same. \<close>
| "less_eq_ctrace (x #\<^sub>C\<^sub>E xs) (y #\<^sub>C\<^sub>E ys) = (x = y \<and> xs \<le> ys)"
-- \<open> Any other case. \<close>
| "less_eq_ctrace X Y = False"

definition less_ctrace :: "'a ctrace \<Rightarrow> 'a ctrace \<Rightarrow> bool" where
"less_ctrace a b = (a \<le> b \<and> \<not>b \<le> a)"

lemma ctrace_refl:
  fixes x :: "'a ctrace"
  shows "x \<le> x"
  apply (induct x rule:ctrace.induct)
  by auto

lemma ctrace_trans:
  fixes x y z :: "'a ctrace"
  shows "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
  apply (induct x z arbitrary:y rule:less_eq_ctrace.induct)
    apply (simp_all)
            apply auto
  apply (case_tac y, auto)
  apply (case_tac y, auto)
            apply (case_tac y, auto)
           apply (case_tac y, auto)
          apply (case_tac ya, auto)
         apply (case_tac ya, auto)
  by (case_tac y, auto)+

lemma ctrace_antisym:
  fixes x y z :: "'a ctrace"
  shows "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
  apply (induct x y rule:less_eq_ctrace.induct, auto)
  by (case_tac s, auto)

instance
  apply intro_classes
     apply (simp_all add:less_ctrace_def)
    apply (simp add:ctrace_refl)
  using ctrace_trans apply blast
  using ctrace_antisym by auto

end

type_synonym 'a cttrace = "('a tevent) listle"

type_synonym 'e cttraces = "('e cttrace) set"

type_synonym 'e CTs = "('e ctrace) set"

text \<open> Healthiness conditions \<close>

definition CT1 :: "'a cttraces \<Rightarrow> bool" where
"CT1 P \<equiv> \<forall>s t. (t \<in> P \<and> s \<le> t) \<longrightarrow> s \<in> P"

definition CT1s :: "'a CTs \<Rightarrow> bool" where
"CT1s P \<equiv> \<forall>s t. (t \<in> P \<and> s \<le> t) \<longrightarrow> s \<in> P"

definition CT0s :: "'a CTs \<Rightarrow> bool" where
"CT0s P \<equiv> P \<noteq> {}"

lemma CT0s_CT1s_imp_nil:
  assumes "CT0s P" "CT1s P"
  shows "\<langle>\<rangle>\<^sub>C \<in> P"
  using assms unfolding CT0s_def CT1s_def
  using less_eq_ctrace.simps(1) by blast

primrec CT2CTock :: "('a ctrace) \<Rightarrow> 'a ctockl" where
"CT2CTock \<langle>\<rangle>\<^sub>C = []" |
"CT2CTock \<langle>[X]\<^sub>R\<rangle>\<^sub>C = [Ref {z. \<exists>y. z = (tockevent.Event y) \<and> y \<in> X}]" |
"CT2CTock (X #\<^sub>C\<^sub>T xs) = (Ref {z. \<exists>y. z = (tockevent.Event y) \<and> y \<in> X}) # ((REvent tock) # CT2CTock xs)" |
"CT2CTock (v #\<^sub>C\<^sub>E xs) = (REvent (tockevent.Event v)) # CT2CTock xs"

fun CTock2CT :: "(('a tockevent) revent) list \<Rightarrow> ('a ctrace)" where
"CTock2CT ((REvent (tockevent.Event a)) # xs) = (a #\<^sub>C\<^sub>E CTock2CT xs)" |
"CTock2CT ((Ref X) # []) = \<langle>[{z. (tockevent.Event z) \<in> X}]\<^sub>R\<rangle>\<^sub>C" |
"CTock2CT ((Ref X) # (REvent tock) # v) = ({z. (tockevent.Event z) \<in> X} #\<^sub>C\<^sub>T CTock2CT v)" |
"CTock2CT X = \<langle>\<rangle>\<^sub>C"

lemma CTock2CT_CT2CTock: "CTock2CT(CT2CTock(A)) = A"
  by (induct A, auto)

lemma "ctockWD (REvent (CTock.Event a) # Aa) = (ctockWD(Aa))"
  by auto

text {* The mapping removes 'tock', but cannot safely add it back, unless
        in a process P there isn't a [Ref {Event a},Event tock] in the trace,
        which indicates that 'tock' must be refused? But what if 'tock' may or
        may not be refused after Ref {Event a} *}

lemma "CT2CTock (CTock2CT([Ref {tock, Event a}])) = [Ref {Event a}]"
  by auto

lemma "CT2CTock (CTock2CT([Ref {Event e}])) = [Ref {Event e}]"
  by auto

lemma 
  assumes "ctockWD A"
  shows "CT2CTock(CTock2CT(A)) = A"
  using assms apply (induct A rule:CTock2CT.induct, auto)
  oops (* doesn't hold *)

definition CTock_H1 :: "'a ctocks \<Rightarrow> bool" where
"CTock_H1 P \<equiv> \<forall>s t. (t \<in> P \<and> CTock_less_le s t) \<longrightarrow> s \<in> P"


definition CTocks2CTs :: "'a ctocks \<Rightarrow> 'a CTs" where
"CTocks2CTs CT = {CTock2CT z |z. z \<in> CT}"

lemma CTocks2CTs_universal_disj: 
  "CTocks2CTs(\<Union> P) = \<Union>{CTocks2CTs z |z. z \<in> P}"
  unfolding CTocks2CTs_def by auto

definition CTs2CTocks :: "'a CTs \<Rightarrow> 'a ctocks" where
"CTs2CTocks C = \<Union>{ct. (CTocks2CTs ct) \<subseteq> C \<and> (\<forall>x. x \<in> ct \<longrightarrow> ctockWD x)}"

lemma CTock2CT_CT2CTock_set:
  assumes "x \<in> P"
  shows "{CTock2CT(CT2CTock(x))} \<subseteq> P"
  by (simp add: CTock2CT_CT2CTock assms)

lemma CTocks2CTs_CTs2CTocks_indu:
  assumes "x \<in> P"
  shows "\<exists>z. x = CTock2CT z \<and> (\<exists>x. {CTock2CT z |z. z \<in> x} \<subseteq> P \<and> z \<in> x)"
proof -
  have "(\<exists>z. x = CTock2CT z \<and> (\<exists>x. {CTock2CT z |z. z \<in> x} \<subseteq> P \<and> z \<in> x))
        =
        (x = CTock2CT(CT2CTock(x)) \<and> (\<exists>y. {CTock2CT z |z. z \<in> y} \<subseteq> P \<and> CT2CTock(x) \<in> y))"
    by (smt CTock2CT_CT2CTock mem_Collect_eq singletonD singletonI subsetCE subsetI)
  also have "... = (\<exists>y. {CTock2CT z |z. z \<in> y} \<subseteq> P \<and> CT2CTock(x) \<in> y)"
    by (auto simp add:CTock2CT_CT2CTock)
  also have "... = ({CTock2CT z |z. z \<in> {CT2CTock(x)}} \<subseteq> P)"
    by auto
  also have "... = ({CTock2CT(CT2CTock(x))} \<subseteq> P)"
    by auto
  also have "... = True"
    by (simp add: CTock2CT_CT2CTock assms)
  finally show ?thesis by auto
qed

lemma CT2CTock_is_ctockWD:
  shows "ctockWD(CT2CTock(x))"
  by (induct x, auto)

lemma CTocks2CTs_CTs2CTocks_indu2:
  assumes "x \<in> P"
  shows "\<exists>z. x = CTock2CT z \<and> (\<exists>x. {CTock2CT z |z. z \<in> x} \<subseteq> P \<and> (\<forall>xa. xa \<in> x \<longrightarrow> ctockWD xa) \<and> z \<in> x)"
proof -
  have "(\<exists>z. x = CTock2CT z \<and> (\<exists>x. {CTock2CT z |z. z \<in> x} \<subseteq> P \<and> (\<forall>xa. xa \<in> x \<longrightarrow> ctockWD xa) \<and> z \<in> x))
        =
        (x = CTock2CT(CT2CTock(x)) \<and> (\<exists>y. {CTock2CT z |z. z \<in> y} \<subseteq> P \<and> (\<forall>xa. xa \<in> y \<longrightarrow> ctockWD xa) \<and> CT2CTock(x) \<in> y))"
    using CTock2CT_CT2CTock
    by (smt CT2CTock_is_ctockWD assms mem_Collect_eq singletonD singletonI subsetI)    
  also have "... = (\<exists>y. {CTock2CT z |z. z \<in> y} \<subseteq> P \<and> (\<forall>xa. xa \<in> y \<longrightarrow> ctockWD xa) \<and> CT2CTock(x) \<in> y)"
    by (auto simp add:CTock2CT_CT2CTock)
  also have "... = (\<exists>y. {CTock2CT z |z. z \<in> y} \<subseteq> P \<and> (y \<subseteq> {xa. ctockWD xa}) \<and> CT2CTock(x) \<in> y)"
    by auto
  also have "... = (\<exists>y. {CTock2CT z |z. z \<in> y \<and> z \<in> {xa. ctockWD xa}} \<subseteq> P \<and> (y \<subseteq> {xa. ctockWD xa}) \<and> CT2CTock(x) \<in> y)"
    apply simp
    by (smt Collect_mem_eq Collect_mono_iff)
  also have "... = (\<exists>y. {CTock2CT z |z. z \<in> y \<and> z \<in> {xa. ctockWD xa}} \<subseteq> P \<and> CT2CTock(x) \<in> y)"
    apply simp
    using CT2CTock_is_ctockWD
    by (smt Collect_mem_eq Collect_mono_iff singletonD singletonI singleton_conv)
  also have "... = ({CTock2CT z |z. z \<in> {CT2CTock(x)} \<and> z \<in> {xa. ctockWD xa}} \<subseteq> P)"
    by blast
  also have "... = True"
    apply auto
    by (simp add: CTock2CT_CT2CTock assms)
  finally show ?thesis by auto
qed

lemma
  shows "\<forall>x. x \<in> CTs2CTocks(P) \<longrightarrow> ctockWD x"
  unfolding CTocks2CTs_def CTs2CTocks_def by auto
  
lemma CTocks2CTs_CTs2CTocks_bij:
  shows "CTocks2CTs(CTs2CTocks(P)) = P"
  unfolding CTocks2CTs_def CTs2CTocks_def apply auto
  by (simp add: CTocks2CTs_CTs2CTocks_indu2)

lemma CTock2CT_in_set_subset:
  shows "{CTock2CT z |z. z \<in> X} \<subseteq> P \<longleftrightarrow> X \<subseteq> {z. CTock2CT z \<in> P}"
proof -
  have "({CTock2CT z |z. z \<in> X} \<subseteq> P)
        =
        (\<forall>y. (\<exists>z. y = CTock2CT z \<and> z \<in> X) \<longrightarrow> y \<in> P)"
    by auto
  also have "... = (\<forall>z. (CTock2CT z \<in> P \<or> z \<notin> X))"
    by auto
  also have "... = (\<forall>z. z \<in> X \<longrightarrow> CTock2CT z \<in> P)"
    by auto
  also have "... = (X \<subseteq> {z. CTock2CT z \<in> P})"
    by auto
  finally show ?thesis .
qed

lemma 
  shows "CTs2CTocks(CTocks2CTs({[]})) \<subseteq> {[]}"
  unfolding CTocks2CTs_def CTs2CTocks_def apply auto
  apply (auto simp add:CTock2CT_in_set_subset)
  apply (case_tac x, auto)
  by (smt CTock2CT.simps(1) CTock2CT.simps(2) CTock2CT.simps(3) ctockWD.elims(2) ctrace.distinct(1) ctrace.distinct(3) ctrace.distinct(5) list.discI mem_Collect_eq subsetCE)

lemma
  assumes "{CTock2CT z |z. z \<in> X} \<subseteq> {CTock2CT z |z. z \<in> P}" "CTock_H1 P"
  and "\<forall>x. x \<in> X \<longrightarrow> ctockWD x"
  shows "X \<subseteq> P"
proof -
  have "({CTock2CT z |z. z \<in> X} \<subseteq> {CTock2CT z |z. z \<in> P})
        =
        (\<forall>y. (\<exists>z. y = CTock2CT z \<and> z \<in> X) \<longrightarrow> (\<exists>z. y = CTock2CT z \<and> z \<in> P))"
    by auto
  also have "... = (\<forall>y z. (y = CTock2CT z \<and> z \<in> X) \<longrightarrow> (\<exists>t. y = CTock2CT t \<and> t \<in> P))"
    by auto
  also have "... = (\<forall>y z. z \<in> X \<longrightarrow> (\<exists>t. CTock2CT z = CTock2CT t \<and> t \<in> P))"
    by auto
  also have "(\<forall>y z. z \<in> X \<longrightarrow> (\<exists>t. CTock2CT z = CTock2CT t \<and> t \<in> P)) 
             \<longrightarrow>
             (\<forall>y z. z \<in> X \<longrightarrow> z \<in> P)"
    apply auto
    using CTock2CT_CT2CTock 
    (* With the definition of CTock2CT it's impossible for this to ever hold as
       information is lost. Likely would need to use CT2CTock instead together
       with a definition like F2, whereby we fix the refusals by considering
       traces that don't lead to 'tock'. *)
oops

lemma 
  assumes "\<forall>x. x \<in> P \<longrightarrow> ctockWD x"
  shows "CTs2CTocks(CTocks2CTs({[Ref {}]})) \<subseteq> {[Ref {}]}"
  unfolding CTocks2CTs_def CTs2CTocks_def apply auto
  apply (auto simp add:CTock2CT_in_set_subset)
  oops
  
end