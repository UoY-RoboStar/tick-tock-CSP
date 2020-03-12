theory RT
  imports Main FL.Finite_Linear
begin

section \<open>Refusal Traces\<close>

datatype 'e rtevent = TickRT | EventRT 'e

datatype 'e rtrefusal = RefNil ("\<bullet>\<^sub>\<R>\<^sub>\<T>") | RefSet "'e set" ("[_]\<^sub>\<R>\<^sub>\<T>")

datatype 'e rttrace  = RTRefusal "'e rtrefusal" ("\<langle>_\<rangle>\<^sub>\<R>\<^sub>\<T>") | RTEvent "'e rtrefusal" "'e" "'e rttrace" ("_ #\<^sub>\<R>\<^sub>\<T> _ #\<^sub>\<R>\<^sub>\<T> _")

fun in_rtrefusal :: "'e \<Rightarrow> 'e rtrefusal \<Rightarrow> bool" (infix "\<in>\<^sub>\<R>\<^sub>\<T>" 50)  where
  "e \<in>\<^sub>\<R>\<^sub>\<T> \<bullet>\<^sub>\<R>\<^sub>\<T> = False" |
  "e \<in>\<^sub>\<R>\<^sub>\<T> [X]\<^sub>\<R>\<^sub>\<T> = (e \<in> X)"

type_synonym 'e rtprocess = "'e rttrace set"

fun rtWF :: "'e rttrace \<Rightarrow> bool" where
  "rtWF \<langle>X\<rangle>\<^sub>\<R>\<^sub>\<T> = True" |
  "rtWF (X #\<^sub>\<R>\<^sub>\<T> e #\<^sub>\<R>\<^sub>\<T> \<rho>) = (\<not> e \<in>\<^sub>\<R>\<^sub>\<T> X \<and> rtWF \<rho>)"

section \<open>Healthiness Conditions\<close>

subsection \<open>MRT0\<close>

definition MRT0 :: "'e rtprocess \<Rightarrow> bool" where
  "MRT0 P = (\<langle> \<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<in> P)"

subsection \<open>RT1\<close>

fun leq_rttrace :: "'e rttrace \<Rightarrow> 'e rttrace \<Rightarrow> bool" (infix "\<le>\<^sub>\<R>\<^sub>\<T>" 50) where
  "\<langle> \<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>             \<le>\<^sub>\<R>\<^sub>\<T> \<sigma>                   = True" |
  "\<langle> [X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>           \<le>\<^sub>\<R>\<^sub>\<T> \<langle> [Y]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>           = (X \<subseteq> Y)" |
  "\<langle> [X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>           \<le>\<^sub>\<R>\<^sub>\<T> \<langle> \<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>             = False" |
  "\<langle> [X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>           \<le>\<^sub>\<R>\<^sub>\<T> ( [Y]\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> b #\<^sub>\<R>\<^sub>\<T> \<sigma>) = (X \<subseteq> Y)" |
  "\<langle> [X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>           \<le>\<^sub>\<R>\<^sub>\<T> ( \<bullet>\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> b #\<^sub>\<R>\<^sub>\<T> \<sigma>)   = False" |
  "( \<bullet>\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> a #\<^sub>\<R>\<^sub>\<T> \<rho>)   \<le>\<^sub>\<R>\<^sub>\<T> ( \<bullet>\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> b #\<^sub>\<R>\<^sub>\<T> \<sigma>)   = (a = b \<and> \<rho> \<le>\<^sub>\<R>\<^sub>\<T> \<sigma>)" |
  "( \<bullet>\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> a #\<^sub>\<R>\<^sub>\<T> \<rho>)   \<le>\<^sub>\<R>\<^sub>\<T> ( [Y]\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> b #\<^sub>\<R>\<^sub>\<T> \<sigma>) = (a = b \<and> \<rho> \<le>\<^sub>\<R>\<^sub>\<T> \<sigma>)" |
  "( [X]\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> a #\<^sub>\<R>\<^sub>\<T> \<rho>) \<le>\<^sub>\<R>\<^sub>\<T> ( [Y]\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> b #\<^sub>\<R>\<^sub>\<T> \<sigma>) = (X \<subseteq> Y \<and> a = b \<and> \<rho> \<le>\<^sub>\<R>\<^sub>\<T> \<sigma>)" |
  "( [X]\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> a #\<^sub>\<R>\<^sub>\<T> \<rho>) \<le>\<^sub>\<R>\<^sub>\<T> ( \<bullet>\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> b #\<^sub>\<R>\<^sub>\<T> \<sigma>)   = False" |
  "( x #\<^sub>\<R>\<^sub>\<T> a #\<^sub>\<R>\<^sub>\<T> \<rho>)     \<le>\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T>                = False"

lemma leq_rttrace_refl: "x \<le>\<^sub>\<R>\<^sub>\<T> x"
  by (induct x, case_tac x, auto, case_tac x1a, auto)

lemma leq_rttrace_trans: "\<And>y. x \<le>\<^sub>\<R>\<^sub>\<T> y \<Longrightarrow> y \<le>\<^sub>\<R>\<^sub>\<T> z \<Longrightarrow> x \<le>\<^sub>\<R>\<^sub>\<T> z"
  apply (induct x z rule:leq_rttrace.induct, auto)
  apply (case_tac y, auto, case_tac x1, auto)
  apply (case_tac y, auto, case_tac x1, auto)
  apply (case_tac y, auto, case_tac x1, auto, case_tac x21, auto)
  apply (case_tac y, auto, case_tac x1, auto, case_tac x21, auto)
  apply (case_tac y, auto, case_tac x21, auto)
  apply (case_tac y, auto, case_tac x21, auto)
  apply (case_tac y, auto, case_tac x21, auto)
  apply (case_tac y, auto, case_tac x21, auto)
  apply (case_tac y, auto, case_tac x21, auto)
  apply (case_tac y, auto, case_tac x21, auto)
  apply (case_tac y, auto, case_tac x21, auto)
  apply (case_tac y, auto, case_tac x21, auto)
  apply (case_tac y, auto, (case_tac ya, auto)+)
  done

lemma leq_rttrace_antisym: "x \<le>\<^sub>\<R>\<^sub>\<T> y \<Longrightarrow> y \<le>\<^sub>\<R>\<^sub>\<T> x \<Longrightarrow> x = y"
  by (induct x y rule:leq_rttrace.induct, auto, case_tac \<sigma>, auto, case_tac x1, auto)

definition RT1 :: "'e rtprocess \<Rightarrow> bool" where
  "RT1 P = (\<forall> \<rho> \<sigma>. \<sigma> \<in> P \<and> \<rho> \<le>\<^sub>\<R>\<^sub>\<T> \<sigma> \<longrightarrow> \<rho> \<in> P)"

subsection \<open>RT2\<close>

datatype 'e rttrace_tail = RTEmptyTail | RTEventTail 'e "'e rttrace" (infixr "##\<^sub>\<R>\<^sub>\<T>" 65)
datatype 'e rttrace_init = RTEmptyInit | RTEventInit "'e rtrefusal" 'e "'e rttrace_init"

fun rttrace_init_eq :: "'e rttrace_init \<Rightarrow> 'e rttrace_init \<Rightarrow> bool" where
  "rttrace_init_eq RTEmptyInit RTEmptyInit = False" |
  "rttrace_init_eq RTEmptyInit (RTEventInit x e \<rho>) = False" |
  "rttrace_init_eq (RTEventInit x e \<rho>) RTEmptyInit = False" |
  "rttrace_init_eq (RTEventInit x e \<rho>) (RTEventInit y f \<sigma>) = rttrace_init_eq \<rho> \<sigma>"

fun rttrace2init :: "'e rttrace \<Rightarrow> 'e rttrace_init" where
  "rttrace2init \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> = RTEmptyInit" |
  "rttrace2init (x #\<^sub>\<R>\<^sub>\<T> a #\<^sub>\<R>\<^sub>\<T> \<rho>) = RTEventInit x a (rttrace2init \<rho>)"

fun rttrace_with_refusal :: "'e rttrace_init \<Rightarrow> 'e rtrefusal \<Rightarrow> 'e rttrace_tail \<Rightarrow> 'e rttrace" ("_ @\<^sub>\<R>\<^sub>\<T> \<langle>_\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> _" [65, 65, 65] 65) where
  "((RTEventInit x a \<rho>) @\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> \<sigma>) = (x #\<^sub>\<R>\<^sub>\<T> a #\<^sub>\<R>\<^sub>\<T> (\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> \<sigma>))" |
  "(RTEmptyInit @\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> (RTEventTail b \<sigma>)) = (y #\<^sub>\<R>\<^sub>\<T> b #\<^sub>\<R>\<^sub>\<T> \<sigma>)" |
  "(RTEmptyInit @\<^sub>\<R>\<^sub>\<T> \<langle>b\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail) = \<langle>b\<rangle>\<^sub>\<R>\<^sub>\<T>"

fun leq_rttrace_init :: "'e rttrace_init \<Rightarrow> 'e rttrace_init \<Rightarrow> bool" where
  "leq_rttrace_init RTEmptyInit \<rho> = True" |
  "leq_rttrace_init (RTEventInit X e \<rho>) RTEmptyInit = False" |
  "leq_rttrace_init (RTEventInit \<bullet>\<^sub>\<R>\<^sub>\<T> e \<rho>) (RTEventInit Y f \<sigma>) = (e = f \<and> leq_rttrace_init \<rho> \<sigma>)" |
  "leq_rttrace_init (RTEventInit [X]\<^sub>\<R>\<^sub>\<T> e \<rho>) (RTEventInit \<bullet>\<^sub>\<R>\<^sub>\<T> f \<sigma>) = False" |
  "leq_rttrace_init (RTEventInit [X]\<^sub>\<R>\<^sub>\<T> e \<rho>) (RTEventInit [Y]\<^sub>\<R>\<^sub>\<T> f \<sigma>) = (X \<subseteq> Y \<and> e = f \<and> leq_rttrace_init \<rho> \<sigma>)"

lemma rttrace_with_refusal_eq1:
  "\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>X\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail = \<sigma> @\<^sub>\<R>\<^sub>\<T> \<langle>Y\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail \<Longrightarrow> \<rho> = \<sigma>"
  by (induct \<rho> \<sigma> rule: rttrace_init_eq.induct, auto)

lemma rttrace_with_refusal_eq2:
  "\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>X\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail = \<sigma> @\<^sub>\<R>\<^sub>\<T> \<langle>Y\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail \<Longrightarrow> X = Y"
  by (induct \<rho> \<sigma> rule: rttrace_init_eq.induct, auto)

lemma rttrace_with_refusal_eq3:
  "\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>X\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> = \<sigma> @\<^sub>\<R>\<^sub>\<T> \<langle>Y\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> f ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> \<Longrightarrow> \<rho> = \<sigma>"
  apply (induct \<rho> \<sigma> rule: rttrace_init_eq.induct, auto)
  apply (metis (full_types) rttrace.simps(4) rttrace_with_refusal.elims rttrace_with_refusal.simps(2))
  using rttrace_with_refusal.elims by blast

definition RT2 :: "'e rtprocess \<Rightarrow> bool" where
  "RT2 P = (\<forall> \<rho> \<sigma> X Y. 
    \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> \<sigma> \<in> P \<and> (\<forall>e\<in>Y. \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<notin> P) 
      \<longrightarrow> \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[X \<union> Y]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> \<sigma> \<in> P)"

subsection \<open>RT3\<close>

fun no_tick :: "'e rtevent rttrace_init \<Rightarrow> bool" where 
  "no_tick RTEmptyInit = True" |
  "no_tick (RTEventInit x (EventRT e) \<rho>) = no_tick \<rho>" |
  "no_tick (RTEventInit x (TickRT) \<rho>) = False"

definition RT3 :: "'e rtevent rtprocess \<Rightarrow> bool" where
  "RT3 P = (\<forall> \<rho> x y e. \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> \<in> P \<longrightarrow> no_tick \<rho>)"

lemma RT3_refusal_after_TickRT:
  "\<And>P. RT3 P \<Longrightarrow> (X #\<^sub>\<R>\<^sub>\<T> TickRT #\<^sub>\<R>\<^sub>\<T> \<rho>) \<in> P \<Longrightarrow> \<exists> Y. \<rho> = \<langle>Y\<rangle>\<^sub>\<R>\<^sub>\<T>"
proof (induct \<rho>, auto)
  fix x1a x2 \<rho> P
  assume in_P: "(X #\<^sub>\<R>\<^sub>\<T> TickRT #\<^sub>\<R>\<^sub>\<T> (x1a #\<^sub>\<R>\<^sub>\<T> x2 #\<^sub>\<R>\<^sub>\<T> \<rho>)) \<in> P"
  assume RT3_P: "RT3 P"

  have "\<exists> \<rho>' x e y. (X #\<^sub>\<R>\<^sub>\<T> TickRT #\<^sub>\<R>\<^sub>\<T> (x1a #\<^sub>\<R>\<^sub>\<T> x2 #\<^sub>\<R>\<^sub>\<T> \<rho>)) = (RTEventInit X TickRT \<rho>' @\<^sub>\<R>\<^sub>\<T> \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T>)"
    apply (induct \<rho>, auto, rule_tac x = RTEmptyInit in exI, auto)
    by (smt rttrace.inject(2) rttrace_init.exhaust rttrace_with_refusal.simps(1) rttrace_with_refusal.simps(2))
  then obtain \<rho>' x e y where "(X #\<^sub>\<R>\<^sub>\<T> TickRT #\<^sub>\<R>\<^sub>\<T> (x1a #\<^sub>\<R>\<^sub>\<T> x2 #\<^sub>\<R>\<^sub>\<T> \<rho>)) = (RTEventInit X TickRT \<rho>' @\<^sub>\<R>\<^sub>\<T> \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T>)"
    by blast
  then have "no_tick (RTEventInit X TickRT \<rho>')"
    using RT3_P in_P unfolding RT3_def by (auto, metis in_P no_tick.simps(3) rttrace_with_refusal.simps(1))
  then show "False"
    by auto
qed

subsection \<open>RT4\<close>

definition RT4 :: "'e rtevent rtprocess \<Rightarrow> bool" where
  "RT4 P = (\<forall> \<rho> x y.
    \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> \<in> P
      \<longrightarrow> x = \<bullet>\<^sub>\<R>\<^sub>\<T> \<and> \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<in> P)"

subsection \<open>RT\<close>

definition RT :: "'e rtevent rtprocess \<Rightarrow> bool" where
  "RT P = ((\<forall>x\<in>P. rtWF x) \<and> MRT0 P \<and> RT1 P \<and> RT2 P \<and> RT3 P \<and> RT4 P)"

definition refinesRT :: "'e rtprocess \<Rightarrow> 'e rtprocess \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>\<R>\<^sub>\<T>" 50) where
  "P \<sqsubseteq>\<^sub>\<R>\<^sub>\<T> Q = (Q \<subseteq> P)"

section \<open>Maximal Healthiness Conditions\<close>

subsection \<open>RTM1 (replaces RT1)\<close>

fun leq_rttrace_max :: "'e rttrace \<Rightarrow> 'e rttrace \<Rightarrow> bool" (infix "\<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M>" 50) where
  "\<langle> \<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>             \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> \<sigma>                   = True" |
  "\<langle> [X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>           \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> \<langle> [Y]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>           = (X = Y)" |
  "\<langle> [X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>           \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> \<langle> \<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>             = False" |
  "\<langle> [X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>           \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> ( [Y]\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> b #\<^sub>\<R>\<^sub>\<T> \<sigma>) = (X = Y)" |
  "\<langle> [X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>           \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> ( \<bullet>\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> b #\<^sub>\<R>\<^sub>\<T> \<sigma>)   = False" |
  "( \<bullet>\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> a #\<^sub>\<R>\<^sub>\<T> \<rho>)   \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> ( \<bullet>\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> b #\<^sub>\<R>\<^sub>\<T> \<sigma>)   = (a = b \<and> \<rho> \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> \<sigma>)" |
  "( \<bullet>\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> a #\<^sub>\<R>\<^sub>\<T> \<rho>)   \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> ( [Y]\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> b #\<^sub>\<R>\<^sub>\<T> \<sigma>) = (a = b \<and> \<rho> \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> \<sigma>)" |
  "( [X]\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> a #\<^sub>\<R>\<^sub>\<T> \<rho>) \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> ( [Y]\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> b #\<^sub>\<R>\<^sub>\<T> \<sigma>) = (X = Y \<and> a = b \<and> \<rho> \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> \<sigma>)" |
  "( [X]\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> a #\<^sub>\<R>\<^sub>\<T> \<rho>) \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> ( \<bullet>\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> b #\<^sub>\<R>\<^sub>\<T> \<sigma>)   = False" |
  "( x #\<^sub>\<R>\<^sub>\<T> a #\<^sub>\<R>\<^sub>\<T> \<rho>)     \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T>                = False"

lemma leq_rttrace_max_refl: "x \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> x"
  by (induct x, case_tac x, auto, case_tac x1a, auto)

lemma leq_rttrace_max_trans: "\<And>y. x \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> y \<Longrightarrow> y \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> z \<Longrightarrow> x \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> z"
  apply (induct x z rule:leq_rttrace.induct, auto)
  apply (case_tac y, auto, case_tac x1, auto)
  apply (case_tac y, auto, case_tac x1, auto)
  apply (case_tac y, auto, case_tac x1, auto)
  apply (case_tac y, auto, case_tac x1, auto, case_tac x21, auto)
  apply (case_tac y, auto, case_tac x1, auto, case_tac x21, auto)
  apply (case_tac y, auto, case_tac x1, auto, case_tac x21, auto)
  apply (case_tac y, auto, case_tac x21, auto)
  apply (case_tac y, auto, case_tac x21, auto)
  apply (case_tac y, auto, case_tac x21, auto)
  apply (case_tac y, auto, case_tac x21, auto)
  apply (case_tac y, auto, case_tac x21, auto)
  apply (case_tac y, auto, case_tac x21, auto)
  apply (case_tac y, auto, case_tac x21, auto)
  apply (case_tac y, auto, case_tac x21, auto)
  apply (case_tac y, auto, case_tac x21, auto)
  apply (case_tac y, auto, (case_tac ya, auto)+)
  done

lemma leq_rttrace_max_antisym: "x \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> y \<Longrightarrow> y \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> x \<Longrightarrow> x = y"
  by (induct x y rule:leq_rttrace.induct, auto, case_tac \<sigma>, auto, case_tac x1, auto)

fun leq_rttrace_init_max :: "'e rttrace_init \<Rightarrow> 'e rttrace_init \<Rightarrow> bool" where
  "leq_rttrace_init_max RTEmptyInit \<rho> = True" |
  "leq_rttrace_init_max (RTEventInit X e \<rho>) RTEmptyInit = False" |
  "leq_rttrace_init_max (RTEventInit \<bullet>\<^sub>\<R>\<^sub>\<T> e \<rho>) (RTEventInit Y f \<sigma>) = (e = f \<and> leq_rttrace_init_max \<rho> \<sigma>)" |
  "leq_rttrace_init_max (RTEventInit [X]\<^sub>\<R>\<^sub>\<T> e \<rho>) (RTEventInit \<bullet>\<^sub>\<R>\<^sub>\<T> f \<sigma>) = False" |
  "leq_rttrace_init_max (RTEventInit [X]\<^sub>\<R>\<^sub>\<T> e \<rho>) (RTEventInit [Y]\<^sub>\<R>\<^sub>\<T> f \<sigma>) = (X \<subseteq> Y \<and> e = f \<and> leq_rttrace_init_max \<rho> \<sigma>)"

fun leq_rttrace_rttrace_init_max :: "'e rttrace \<Rightarrow> 'e rttrace_init \<Rightarrow> bool" where
  "leq_rttrace_rttrace_init_max \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> RTEmptyInit = False" |
  "leq_rttrace_rttrace_init_max (v #\<^sub>\<R>\<^sub>\<T> va #\<^sub>\<R>\<^sub>\<T> vb) RTEmptyInit = False" |
  "leq_rttrace_rttrace_init_max \<langle>vc\<rangle>\<^sub>\<R>\<^sub>\<T> (RTEventInit v va vb) = (vc = v)" |
  "leq_rttrace_rttrace_init_max (v #\<^sub>\<R>\<^sub>\<T> va #\<^sub>\<R>\<^sub>\<T> vb) (RTEventInit vc vd ve) = (v = vc \<and> va = vd \<and> leq_rttrace_rttrace_init_max vb ve)"

definition RTM1 :: "'e rtprocess \<Rightarrow> bool" where
  "RTM1 P = (\<forall> \<rho> \<sigma>. \<sigma> \<in> P \<and> \<rho> \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> \<sigma> \<longrightarrow> \<rho> \<in> P)"

lemma RTM1_init_event:
  assumes "RTM1 P"
  shows "RTM1 {\<rho>. (x #\<^sub>\<R>\<^sub>\<T> a #\<^sub>\<R>\<^sub>\<T> \<rho>) \<in> P}"
  using assms unfolding RTM1_def apply auto
  by (metis leq_rttrace_max.simps(6) leq_rttrace_max.simps(8) rtrefusal.exhaust)

subsection \<open>RTM2 (replaces RT2)\<close>

definition RTM2 :: "'e rtprocess \<Rightarrow> bool" where
  "RTM2 P = (\<forall> \<rho> X e. \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail \<in> P \<and> e \<notin> X \<longrightarrow> \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<in> P)"

subsection \<open>RTM\<close>

definition RTM :: "'e rtevent rtprocess \<Rightarrow> bool" where
  "RTM P = ((\<forall>x\<in>P. rtWF x) \<and> MRT0 P \<and> RTM1 P \<and> RTM2 P \<and> RT3 P \<and> RT4 P)"

end