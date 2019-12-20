theory RT
  imports Main FL.Finite_Linear
begin

section \<open>Refusal Traces\<close>

datatype 'e rtevent = TickRT | EventRT 'e

datatype 'e rtrefusal = RefNil ("\<bullet>\<^sub>\<R>\<^sub>\<T>") | RefSet "'e set" ("[_]\<^sub>\<R>\<^sub>\<T>")

datatype 'e rttrace  = RTRefusal "'e rtrefusal" ("\<langle>_\<rangle>\<^sub>\<R>\<^sub>\<T>") | RTEvent "'e rtrefusal" "'e" "'e rttrace" ("_ #\<^sub>\<R>\<^sub>\<T> _ #\<^sub>\<R>\<^sub>\<T> _")

type_synonym 'e rtprocess = "'e rttrace set"

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

definition RT1 :: "'e rtprocess \<Rightarrow> bool" where
  "RT1 P = (\<forall> \<rho> \<sigma>. \<sigma> \<in> P \<and> \<rho> \<le>\<^sub>\<R>\<^sub>\<T> \<sigma> \<longrightarrow> \<rho> \<in> P)"

subsection \<open>RT2\<close>

datatype 'e rttrace_tail = RTEmptyTail | RTEventTail 'e "'e rttrace" (infixr "##\<^sub>\<R>\<^sub>\<T>" 65)
datatype 'e rttrace_init = RTEmptyInit | RTEventInit "'e rtrefusal" 'e "'e rttrace_init"

fun rttrace_with_refusal :: "'e rttrace_init \<Rightarrow> 'e rtrefusal \<Rightarrow> 'e rttrace_tail \<Rightarrow> 'e rttrace" ("_ @\<^sub>\<R>\<^sub>\<T> \<langle>_\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> _" [65, 65, 65] 65) where
  "((RTEventInit x a \<rho>) @\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> \<sigma>) = (x #\<^sub>\<R>\<^sub>\<T> a #\<^sub>\<R>\<^sub>\<T> (\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> \<sigma>))" |
  "(RTEmptyInit @\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> (RTEventTail b \<sigma>)) = (y #\<^sub>\<R>\<^sub>\<T> b #\<^sub>\<R>\<^sub>\<T> \<sigma>)" |
  "(RTEmptyInit @\<^sub>\<R>\<^sub>\<T> \<langle>b\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail) = \<langle>b\<rangle>\<^sub>\<R>\<^sub>\<T>"

definition RT2 :: "'e rtprocess \<Rightarrow> bool" where
  "RT2 P = (\<forall> \<rho> \<sigma> X Y. 
    \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> \<sigma> \<in> P \<and> (\<forall>e\<in>Y. \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<in> P) 
      \<longrightarrow> \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[X \<union> Y]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> \<sigma> \<in> P)"

subsection \<open>RT3\<close>

fun no_tick :: "'e rtevent rttrace_init \<Rightarrow> bool" where 
  "no_tick RTEmptyInit = True" |
  "no_tick (RTEventInit x (EventRT e) \<rho>) = no_tick \<rho>" |
  "no_tick (RTEventInit x (TickRT) \<rho>) = False"

definition RT3 :: "'e rtevent rtprocess \<Rightarrow> bool" where
  "RT3 P = (\<forall> \<rho> x y e. \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> \<in> P \<longrightarrow> no_tick \<rho>)"

subsection \<open>RT4\<close>

definition RT4 :: "'e rtevent rtprocess \<Rightarrow> bool" where
  "RT4 P = (\<forall> \<rho> x y.
    \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> \<in> P
      \<longrightarrow> x = \<bullet>\<^sub>\<R>\<^sub>\<T> \<and> \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<in> P)"

section \<open>Maximal Healthiness Conditions\<close>

subsection \<open>RTM1 (replaces RT1)\<close>

fun leq_rttrace_max :: "'e rttrace \<Rightarrow> 'e rttrace \<Rightarrow> bool" (infix "\<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M>" 50) where
  "\<langle> \<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>             \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> \<sigma>                   = True" |
  "\<langle> [X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>           \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> \<langle> [Y]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>           = (X = Y)" |
  "\<langle> [X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>           \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> \<langle> \<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>             = False" |
  "\<langle> [X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>           \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> ( [Y]\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> b #\<^sub>\<R>\<^sub>\<T> \<sigma>) = (X = Y)" |
  "\<langle> [X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>           \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> ( \<bullet>\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> b #\<^sub>\<R>\<^sub>\<T> \<sigma>)   = False" |
  "( \<bullet>\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> a #\<^sub>\<R>\<^sub>\<T> \<rho>)   \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> ( \<bullet>\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> b #\<^sub>\<R>\<^sub>\<T> \<sigma>)   = (a = b \<and> \<rho> \<le>\<^sub>\<R>\<^sub>\<T> \<sigma>)" |
  "( \<bullet>\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> a #\<^sub>\<R>\<^sub>\<T> \<rho>)   \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> ( [Y]\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> b #\<^sub>\<R>\<^sub>\<T> \<sigma>) = (a = b \<and> \<rho> \<le>\<^sub>\<R>\<^sub>\<T> \<sigma>)" |
  "( [X]\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> a #\<^sub>\<R>\<^sub>\<T> \<rho>) \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> ( [Y]\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> b #\<^sub>\<R>\<^sub>\<T> \<sigma>) = (X = Y \<and> a = b \<and> \<rho> \<le>\<^sub>\<R>\<^sub>\<T> \<sigma>)" |
  "( [X]\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> a #\<^sub>\<R>\<^sub>\<T> \<rho>) \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> ( \<bullet>\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> b #\<^sub>\<R>\<^sub>\<T> \<sigma>)   = False" |
  "( x #\<^sub>\<R>\<^sub>\<T> a #\<^sub>\<R>\<^sub>\<T> \<rho>)     \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T>                = False"

definition RTM1 :: "'e rtprocess \<Rightarrow> bool" where
  "RTM1 P = (\<forall> \<rho> \<sigma>. \<sigma> \<in> P \<and> \<rho> \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> \<sigma> \<longrightarrow> \<rho> \<in> P)"

subsection \<open>RTM2 (replaces RT2)\<close>

definition RTM2 :: "'e rtprocess \<Rightarrow> bool" where
  "RTM2 P = (\<forall> \<rho> X e. \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail \<in> P \<and> e \<notin> X \<longrightarrow> \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<in> P)"