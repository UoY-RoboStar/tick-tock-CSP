theory Failures_BasicOps

imports
  Failures_Core
begin

text \<open> Some operators \<close>

subsection \<open> Div \<close>

definition DivF :: "'a process" ("div\<^sub>F")
  where "div\<^sub>F = ({},{[]})"

lemma T0_Div[simp]:"T0 div\<^sub>F"
  unfolding T0_def DivF_def traces_def by auto

lemma T1_Div[simp]:"T1 div\<^sub>F"
  unfolding T1_def DivF_def traces_def by auto

lemma T2_Div[simp]:"T2 div\<^sub>F"
  unfolding T2_def DivF_def traces_def by auto

lemma F2_Div[simp]:"F2 div\<^sub>F"
  unfolding F2_def DivF_def traces_def by auto

lemma F3_Div[simp]:"F3 div\<^sub>F"
  unfolding F3_def DivF_def traces_def by auto

lemma F4_Div[simp]:"F4 div\<^sub>F"
  unfolding F4_def DivF_def traces_def by auto

lemma F5_Div[simp]:"F5 div\<^sub>F"
  unfolding F5_def DivF_def traces_def by auto

lemma F6_Div[simp]:"F6 div\<^sub>F"
  unfolding F6_def DivF_def traces_def by auto

lemma Div_top:
  assumes "T1 P"
  shows "P \<sqsubseteq> div\<^sub>F"
  using assms unfolding refines_def DivF_def T1_def traces_def by auto

subsection \<open> Unstable Skip \<close>

definition SkipUF :: "'a process" ("Skip\<^sub>U\<^sub>F")
  where "Skip\<^sub>U\<^sub>F = ({},{[],[tick]})"

subsection \<open> Stop \<close>

definition StopF :: "'a process" ("Stop\<^sub>F")
  where "Stop\<^sub>F = ({(t,X). t = [] \<and> X \<subseteq> UNIV},{[]})"

subsection \<open> Prefix \<close>

definition PrefixF :: "'a \<Rightarrow> 'a process \<Rightarrow> 'a process" (infixr "\<rightarrow>\<^sub>F" 61) 
  where "PrefixF e P = ({(s,X). s = [] \<and> evt e \<notin> X} \<union> {(z,X). \<exists>s. z = [evt e]@s \<and> (s,X) \<in> (fst P)},{[]}\<union>{z. \<exists>s. z = [evt e]@s \<and> s \<in> snd P})"

subsection \<open> Internal choice \<close>

definition IntChoice :: "'a process set \<Rightarrow> 'a process" ("\<Sqinter>")
  where "IntChoice P = (\<Union>(fst`P),\<Union>(snd`P))"

definition intChoice :: "'a process \<Rightarrow> 'a process \<Rightarrow> 'a process" (infix "\<sqinter>" 60)
  where "P \<sqinter> Q = (fst P \<union> fst Q, snd P \<union> snd Q)"

lemma intInt_Choices: "P \<sqinter> Q = \<Sqinter>{P,Q}"
  unfolding intChoice_def IntChoice_def by auto

subsection \<open> External choice \<close>

definition ExtChoiceF :: "'a process \<Rightarrow> 'a process \<Rightarrow> 'a process" (infix "\<box>\<^sub>F" 57)
  where "P \<box>\<^sub>F Q = ({(s,X). s = [] \<and> (s,X) \<in> fst P \<inter> fst Q} \<union> {(s,X). (s,X) \<in> fst P \<union> fst Q \<and> s \<noteq> []},snd P \<union> snd Q)"

subsection \<open> Sequential composition \<close>

definition SeqCompF :: "'a process \<Rightarrow> 'a process \<Rightarrow> 'a process" (infix ";\<^sub>F" 57)
  where "P ;\<^sub>F Q = ({(s,X). tick \<notin> set s \<and> (s,X) \<in> fst P} \<union> {(z,X). \<exists>s t. z = s@t \<and> s@[tick] \<in> snd P \<and> (t,X) \<in> fst Q},
                   {z. \<exists>s. tick \<notin> set s \<and> s \<in> snd P} \<union> {z. \<exists>s t. z = s@t \<and> s@[tick] \<in> snd P \<and> t \<in> snd Q})"

subsection \<open> Parallel composition \<close>

function merge_traceF :: "'a trace \<Rightarrow> 'a evt set \<Rightarrow> 'a trace \<Rightarrow> 'a trace set" (infix "\<lbrakk>_\<rbrakk>\<^sup>T\<^sub>F" 55) where
"           ([]  \<lbrakk>X\<rbrakk>\<^sup>T\<^sub>F []) = {[]}" |

"x \<in> X \<Longrightarrow>  ([] \<lbrakk>X\<rbrakk>\<^sup>T\<^sub>F (x#s)) = {}" |
"x \<notin> X \<Longrightarrow>  ([] \<lbrakk>X\<rbrakk>\<^sup>T\<^sub>F (x#s)) = {z. \<exists>u. z = x#u \<and> u \<in> [] \<lbrakk>X\<rbrakk>\<^sup>T\<^sub>F s}" | (* Case not defined well in the book *)

" ((x#s) \<lbrakk>X\<rbrakk>\<^sup>T\<^sub>F []) = [] \<lbrakk>X\<rbrakk>\<^sup>T\<^sub>F (x#s)" |

"y \<notin> X \<Longrightarrow> y' \<notin> X  \<Longrightarrow> ((y#s) \<lbrakk>X\<rbrakk>\<^sup>T\<^sub>F (y'#t)) = {z. \<exists>u. z = y#u \<and> u \<in> s \<lbrakk>X\<rbrakk>\<^sup>T\<^sub>F y'#t}\<union>{z. \<exists>u. z = y'#u \<and> u \<in> y#s \<lbrakk>X\<rbrakk>\<^sup>T\<^sub>F t}" |

"x \<in> X \<Longrightarrow> y \<notin> X  \<Longrightarrow> ((x#s) \<lbrakk>X\<rbrakk>\<^sup>T\<^sub>F (y#t)) = {z. \<exists>u. z = y#u \<and> u \<in> x#s \<lbrakk>X\<rbrakk>\<^sup>T\<^sub>F t} " |
"y \<notin> X \<Longrightarrow> x \<in> X  \<Longrightarrow> ((y#t) \<lbrakk>X\<rbrakk>\<^sup>T\<^sub>F (x#s)) = {z. \<exists>u. z = y#u \<and> u \<in> t \<lbrakk>X\<rbrakk>\<^sup>T\<^sub>F x#s}" |

"x \<in> X \<Longrightarrow> x' \<in> X \<Longrightarrow> x \<noteq> x' \<Longrightarrow> ((x#s) \<lbrakk>X\<rbrakk>\<^sup>T\<^sub>F x'#t) = {}"|
"x \<in> X \<Longrightarrow>  ((x#s) \<lbrakk>X\<rbrakk>\<^sup>T\<^sub>F (x#t)) = {z. \<exists>u. z = x#u \<and> u \<in> s \<lbrakk>X\<rbrakk>\<^sup>T\<^sub>F t} "

proof (auto, atomize_elim, simp_all)
  fix a b::"'a evt list"
  fix aa::"'a evt set"

  show "a = [] \<and> b = [] \<or>
       (\<exists>x. x \<in> aa \<and> a = [] \<and> (\<exists>s. b = x # s)) \<or>
       (\<exists>x. x \<notin> aa \<and> a = [] \<and> (\<exists>s. b = x # s)) \<or>
       (\<exists>x s. a = x # s) \<and> b = [] \<or>
       (\<exists>y X. y \<notin> X \<and> (\<exists>y'. y' \<notin> X \<and> (\<exists>s. a = y # s) \<and> aa = X \<and> (\<exists>t. b = y' # t))) \<or>
       (\<exists>x X. x \<in> X \<and> (\<exists>y. y \<notin> X \<and> (\<exists>s. a = x # s) \<and> aa = X \<and> (\<exists>t. b = y # t))) \<or>
       (\<exists>y X. y \<notin> X \<and> (\<exists>x. x \<in> X \<and> (\<exists>t. a = y # t) \<and> aa = X \<and> (\<exists>s. b = x # s))) \<or>
       (\<exists>x X. x \<in> X \<and> (\<exists>x'. x' \<in> X \<and> x \<noteq> x' \<and> (\<exists>s. a = x # s) \<and> aa = X \<and> (\<exists>t. b = x' # t))) \<or>
       (\<exists>x. x \<in> aa \<and> (\<exists>s. a = x # s) \<and> (\<exists>t. b = x # t))"
    proof (cases a)
      case a_Nil:Nil
      then show ?thesis 
      proof (cases b)
        case c_Nil:Nil 
        then show ?thesis using a_Nil by auto
      next
        case (Cons cx list)
        then show ?thesis using a_Nil a_Nil by auto
      qed
    next
      case (Cons ca list)
      then show ?thesis 
        by (metis neq_Nil_conv)
    qed
  qed
termination by lexicographic_order

thm merge_traceF.induct (* 9 cases only! *)
thm merge_traceF.cases

lemma merge_traceF_comm:
  "(s \<lbrakk>X\<rbrakk>\<^sup>T\<^sub>F t) = (t \<lbrakk>X\<rbrakk>\<^sup>T\<^sub>F s)" 
proof (induct s X t rule:merge_traceF.induct)
  case (1 X)
  then show ?case using merge_traceF.simps(4) by auto
next
  case (2 x X s)
  then show ?case using merge_traceF.simps(4) by auto
next
  case (3 x X s)
  then show ?case using merge_traceF.simps(4) by blast
next
  case (4 x s X)
  then show ?case using merge_traceF.simps(4) by blast
next
  case (5 y X y' s t)
  then have "((y#s) \<lbrakk>X\<rbrakk>\<^sup>T\<^sub>F (y'#t)) = {y # u |u. u \<in> s \<lbrakk>X\<rbrakk>\<^sup>T\<^sub>F y'#t} \<union> {y' # u |u. u \<in> y#s \<lbrakk>X\<rbrakk>\<^sup>T\<^sub>F t}"
    using merge_traceF.simps(5) by blast

  then show ?case
    apply auto
      apply (smt "5.hyps"(1) "5.hyps"(2) "5.hyps"(3) UnCI append_Cons append_self_conv2 mem_Collect_eq merge_traceF.simps(5))
    apply (simp add: "5.hyps"(1) "5.hyps"(2) "5.hyps"(4))
    using "5.hyps"(1) "5.hyps"(2) "5.hyps"(3) "5.hyps"(4) by auto
next
  case (6 x X y s t)
  then have "x # s \<lbrakk>X\<rbrakk>\<^sup>T\<^sub>F y # t = {z. \<exists>u. z = y#u \<and> u \<in> x#s \<lbrakk>X\<rbrakk>\<^sup>T\<^sub>F t}"
    by auto
  then show ?case
    apply auto
    by (simp add: "6.hyps"(1) "6.hyps"(2) "6.hyps"(3))+
next
  case (7 y X x t s)
  then show ?case 
    apply (cases t)
    using merge_traceF.simps(6) merge_traceF.simps(7) by fastforce+
next
  case (8 x X x' s t)
  then show ?case using merge_traceF.simps(8) by blast
next
  case (9 x X s t)
  then show ?case by auto
qed

text \<open> Note that the following definition of parallel composition differs slightly from the 
       book, as 'tick' needs to be synchronised necessarily, when using the trace merge function. \<close>

definition ParCompF :: "'a process \<Rightarrow> ('a set) \<Rightarrow> 'a process \<Rightarrow> 'a process" (infix "\<lbrakk>_\<rbrakk>\<^sub>F" 55)
  where "(P \<lbrakk>X\<rbrakk>\<^sub>F Q) = ({(u,F). \<exists>Y Z. F = Y \<union> Z \<and> Y-(evt`X\<union>{tick}) = Z-(evt`X\<union>{tick}) 
                        \<and> (\<exists>s t. (s,Y) \<in> fst P \<and> (t,Z) \<in> fst Q \<and> u \<in> s \<lbrakk>evt`X\<union>{tick}\<rbrakk>\<^sup>T\<^sub>F t)}
                      \<union> {(u,F). \<exists>s t A G. A \<subseteq> X \<and> F = G \<union> evt ` A \<and> u \<in> (s \<lbrakk>evt`X\<union>{tick}\<rbrakk>\<^sup>T\<^sub>F t) \<and> (s@[tick]) \<in> snd P \<and> (t,G) \<in> fst Q}
                      \<union> {(u,F). \<exists>s t A G. A \<subseteq> X \<and> F = G \<union> evt ` A \<and> u \<in> (s \<lbrakk>evt`X\<union>{tick}\<rbrakk>\<^sup>T\<^sub>F t) \<and> (t@[tick]) \<in> snd Q \<and> (s,G) \<in> fst P},
                      (\<Union>{z. \<exists>s t. z = (s \<lbrakk>evt`X\<union>{tick}\<rbrakk>\<^sup>T\<^sub>F t) \<and> s \<in> snd P \<and> t \<in> snd Q}))"

lemma merge_traceF_empty:
  "([] \<lbrakk>{e}\<rbrakk>\<^sup>T\<^sub>F xs @ [e]) = {}"
  apply (induct xs, auto)
  by (smt insert_Diff insert_not_empty mem_Collect_eq merge_traceF.simps(2) merge_traceF.simps(3))

lemma merge_traceF_singleton:
  assumes "set xs \<inter> X = {}"
  shows "([] \<lbrakk>X\<rbrakk>\<^sup>T\<^sub>F xs) = {xs}"
  using assms by (induct xs, auto)

lemma merge_traceF_Nil_prefix:
  assumes "x \<in> ([] \<lbrakk>X\<rbrakk>\<^sup>T\<^sub>F t)"
  shows "prefix x t" 
  using assms apply (induct x t rule:list_induct2', auto)
  by (smt empty_iff list.inject mem_Collect_eq merge_traceF.simps(2) merge_traceF.simps(3))+

lemma merge_traceF_singleton_prefix:
  assumes "x \<in> ([y] \<lbrakk>X\<rbrakk>\<^sup>T\<^sub>F t)" "y \<in> X"
  shows "prefix x t" 
  using assms apply (induct x t rule:list_induct2', auto)
   apply (smt empty_iff list.inject mem_Collect_eq merge_traceF.simps(6) merge_traceF.simps(8) merge_traceF.simps(9))
  by (smt equals0D list.inject mem_Collect_eq merge_traceF.simps(7) merge_traceF.simps(8) merge_traceF.simps(9) merge_traceF_Nil_prefix merge_traceF_comm)

lemma mergeF_tick_last_tick:
  assumes "Tick_last t" "last t = tick" "t \<noteq> []"
  shows "([tick] \<lbrakk>{tick}\<rbrakk>\<^sup>T\<^sub>F t) = {t}"
  using assms apply (induct t rule:Tick_last.induct, auto)
  by (metis empty_iff evt.distinct(1) insert_iff)+

lemma Tick_last_not_last_tick:
  assumes "Tick_last t" "last t \<noteq> tick"
  shows "tick \<notin> set t"
  using assms apply (induct t rule:Tick_last.induct, auto)
  by (metis empty_iff empty_set)

lemma mergeF_Tick_last_not_last_tick:
  assumes "Tick_last t" "last t \<noteq> tick"
  shows "([] \<lbrakk>{tick}\<rbrakk>\<^sup>T\<^sub>F t) = {t}"
  using assms 
  by (simp add: Tick_last_not_last_tick merge_traceF_singleton)

lemma mergeF_tick_no_tick:
  assumes "tick \<notin> set t"
  shows "([tick] \<lbrakk>{tick}\<rbrakk>\<^sup>T\<^sub>F t) = {}"
  using assms apply (induct t, simp_all)
  by auto

lemma SkipUF_traces_parallel_eq:
  assumes "T1 P" "T0 P"
  shows "(\<Union> {s \<lbrakk>{tick}\<rbrakk>\<^sup>T\<^sub>F t |s t. (s = [] \<or> s = [tick]) \<and> t \<in> snd P}) = snd P"
proof (auto)
  fix x t
  assume "x \<in> [] \<lbrakk>{tick}\<rbrakk>\<^sup>T\<^sub>F t" "t \<in> snd P"
  then show "x \<in> snd P"
    using assms merge_traceF_Nil_prefix T1_def traces_def by blast
next
  fix x t
  assume "x \<in> [tick] \<lbrakk>{tick}\<rbrakk>\<^sup>T\<^sub>F t" "t \<in> snd P"
  then show "x \<in> snd P"
    using assms merge_traceF_singleton_prefix T1_def traces_def by blast 
next
  fix x
  assume assm1: "x \<in> snd P"
  have "Tick_last x"
    using assm1 assms T0_def traces_def by blast
  then show "\<exists>xa. (\<exists>s t. xa = s \<lbrakk>{tick}\<rbrakk>\<^sup>T\<^sub>F t \<and> (s = [] \<or> s = [tick]) \<and> t \<in> snd P) \<and> x \<in> xa"
  proof (cases x)
    case Nil
    then show ?thesis 
      apply (rule_tac x="{[]}" in exI, auto)
      apply (rule_tac x="[]" in exI, auto)
      apply (rule_tac x="[]" in exI, auto)
      using assms T1_def assm1 by blast
  next
    case (Cons a list)
    then show ?thesis 
    proof (cases "last (a#list) = tick")
      case True
      then show ?thesis using Cons assm1 True \<open>Tick_last x\<close> mergeF_tick_last_tick by blast
    next
      case False
      then show ?thesis using Cons assm1 False mergeF_Tick_last_not_last_tick
        using \<open>Tick_last x\<close> by blast
    qed  
  qed
qed

lemma SkipUF_failures_parallel_eq:
  assumes "T1 P" "T0 P" "T2 P" "F6 P"
  shows "{(u, F). \<exists>t. u \<in> ([] \<lbrakk>{tick}\<rbrakk>\<^sup>T\<^sub>F t) \<and> (t, F) \<in> fst P} = fst P"
proof (auto)
  fix a b t
  assume assm1:"a \<in> [] \<lbrakk>{tick}\<rbrakk>\<^sup>T\<^sub>F t" 
    and  assm2:"(t, b) \<in> fst P"

  have "Tick_last t"
    using assm1 assms T0_def traces_def T2_def assm2 by blast

  show "(a, b) \<in> fst P"
  proof (cases "tick \<in> set t")
    case True
    then show ?thesis 
      by (metis Tick_last_not_last_tick \<open>Tick_last t\<close> append_butlast_last_id assm1 equals0D merge_traceF_empty set_empty)
  next
    case False
    then show ?thesis 
      by (metis \<open>Tick_last t\<close> assm1 assm2 empty_iff insert_iff last_in_set mergeF_Tick_last_not_last_tick merge_traceF.simps(1))
  qed
next
  fix a b
  assume assm1:"(a, b) \<in> fst P"

  have "Tick_last a"
    using assm1 assms T0_def traces_def T2_def assms by blast

  have "tick \<notin> set a"
    by (metis F6_def Tick_last_not_last_tick \<open>Tick_last a\<close> append_butlast_last_id assm1 assms(4) empty_iff set_empty)

  then show "\<exists>t. a \<in> [] \<lbrakk>{tick}\<rbrakk>\<^sup>T\<^sub>F t \<and> (t, b) \<in> fst P"
    using assm1
    by (metis \<open>Tick_last a\<close> insertI1 last_in_set mergeF_Tick_last_not_last_tick merge_traceF.simps(1))
qed

text \<open> Below we show that SkipUF is a unit for interleaving. This is important, as the definition of
       the failures semantics of ParCompF contains two additional sets in a union, that handle
       the termination of SkipUF so as to allow failures of P to be propagated. \<close>

lemma SkipUF_ParCompF_unit:
  assumes "T1 P" "T0 P" "T2 P" "F6 P"
  shows ParCompF_Skip: "(Skip\<^sub>U\<^sub>F \<lbrakk>{}\<rbrakk>\<^sub>F P) = P" 
  using assms unfolding ParCompF_def SkipUF_def apply auto
  using SkipUF_traces_parallel_eq SkipUF_failures_parallel_eq
  by (simp add: SkipUF_failures_parallel_eq SkipUF_traces_parallel_eq)

lemma ParCompF_comm: "(P \<lbrakk>X\<rbrakk>\<^sub>F Q) = Q \<lbrakk>X\<rbrakk>\<^sub>F P"
  unfolding ParCompF_def apply safe
     apply (metis Un_commute merge_traceF_comm)
      apply (metis Un_commute merge_traceF_comm)
  using merge_traceF_comm apply fastforce
  apply (metis Un_commute merge_traceF_comm)
using merge_traceF_comm by fastforce+

lemma ParCompF_assoc: "(P \<lbrakk>X\<rbrakk>\<^sub>F (Q \<lbrakk>X\<rbrakk>\<^sub>F R)) = (P \<lbrakk>X\<rbrakk>\<^sub>F Q) \<lbrakk>X\<rbrakk>\<^sub>F R"
  unfolding ParCompF_def apply safe
  oops (* FIXME: Proof probably requires healthiness conditions. *)

lemma ParCompF_dist: "(P \<lbrakk>X\<rbrakk>\<^sub>F (Q \<sqinter> R)) = (P \<lbrakk>X\<rbrakk>\<^sub>F Q) \<sqinter> (P \<lbrakk>X\<rbrakk>\<^sub>F R)"
  unfolding ParCompF_def intChoice_def apply auto
  apply fastforce
  apply fastforce
  by blast

subsection \<open> Interrupt \<close>

definition InterruptF :: "'a process \<Rightarrow> 'a process \<Rightarrow> 'a process" (infix "\<triangle>\<^sub>F" 57)
  where "P \<triangle>\<^sub>F Q = ({(s,X). (s,X) \<in> fst P \<and> ([],X) \<in> fst Q} \<union> {(z,X). \<exists>s t. z = s@t \<and> s \<in> snd P \<and> (t,X) \<in> fst Q \<and> t \<noteq> []},
                   snd P \<union> {z. \<exists>s t. z = s@t \<and> s \<in> snd P \<and> t \<in> snd Q})"

subsection \<open> Renaming \<close>

term List.map
term evt.map_evt

definition RenamingF :: "'a process \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b process" ("_\<lbrakk>_\<rbrakk>\<^sub>F" 57)
  where "P\<lbrakk>R\<rbrakk>\<^sub>F = ({(s',X). \<exists>s. map (evt.map_evt R) s = s' \<and> (s,(inv (evt.map_evt R))`X) \<in> fst P},
                 {s'. \<exists>s. map (evt.map_evt R) s = s' \<and> s \<in> snd P})"

subsection \<open> Hiding \<close>

definition HideF :: "'a process \<Rightarrow> 'a set \<Rightarrow> 'a process" (infix "\\\<^sub>F" 57)
  where "P \\\<^sub>F X = ({(t,Y). \<exists>s. (s,Y \<union> evt`X) \<in> fst P \<and> t = filter (\<lambda>e. e \<notin> evt`X) s},
                    {t. \<exists>z. t = filter (\<lambda>e. e \<notin> evt`X) z \<and> z \<in> snd P})"

end