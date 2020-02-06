theory TickTock_Pri
  imports TickTock.TickTock Utils.Event_Priority
begin

text \<open> This theory defines a simplified version of PriTT1, providing a definitive
       definition for Pri in TickTock. \<close>

definition prirefTT :: "('e ttevent) partialorder \<Rightarrow> ('e ttobs) list \<Rightarrow> ('e ttobs) list set \<Rightarrow> ('e ttevent) set \<Rightarrow> ('e ttevent) set" where
"prirefTT p \<sigma> Q S = 
  (S \<union> {e. (\<sigma> @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> e <\<^sup>*p Tock)} 
     \<union> {e. (\<exists>b. b \<notin> S \<and> \<sigma> @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> e <\<^sup>*p b)})"

function (sequential) priTT :: "('e ttevent) partialorder \<Rightarrow> ('e ttobs) list \<Rightarrow> ('e ttobs) list \<Rightarrow> ('e ttobs) list \<Rightarrow> ('e ttobs) list set \<Rightarrow> bool" where
"priTT p [] [] \<sigma> Q = True" |
"priTT p [[R]\<^sub>R] [[S]\<^sub>R] \<sigma> Q = (R \<subseteq> prirefTT p \<sigma> Q S)" |
"priTT p ([R]\<^sub>R # [Tock]\<^sub>E # aa) ([S]\<^sub>R # [Tock]\<^sub>E # zz) \<sigma> Q =
   ((R \<subseteq> prirefTT p \<sigma> Q S) \<and> Tock \<notin> prirefTT p \<sigma> Q S \<and> priTT p aa zz (\<sigma> @ [[S]\<^sub>R,[Tock]\<^sub>E]) Q)" |
"priTT p ([e\<^sub>1]\<^sub>E # aa) ([e\<^sub>2]\<^sub>E # zz) \<sigma> Q
 = 
 (e\<^sub>1 = e\<^sub>2 \<and> priTT p aa zz (\<sigma> @ [[e\<^sub>1]\<^sub>E]) Q \<and>
  (maximal(p,e\<^sub>2) 
   \<or> 
  (\<exists>Z. \<sigma> @ [[Z]\<^sub>R] \<in> Q \<and> e\<^sub>2 \<noteq> Tick \<and> e\<^sub>2 \<notin> prirefTT p \<sigma> Q Z)))" |
"priTT p x y \<sigma> Q = False"
  by (pat_completeness, simp_all)
termination by lexicographic_order

text \<open> Pretty syntax introduced below for convenience. \<close>

syntax 
  "_priTT" :: " ('e ttobs) list \<Rightarrow> 
                ('e ttevent) partialorder \<Rightarrow> 
                ('e ttobs) list \<Rightarrow> 
                ('e ttobs) list set \<Rightarrow>
                ('e ttobs) list \<Rightarrow> bool" ("_ priTT\<^sub>[\<^sub>_\<^sub>,\<^sub>_\<^sub>,\<^sub>_\<^sub>] _" [51,51,51,51,51])

translations
  "x priTT\<^sub>[\<^sub>p\<^sub>,\<^sub>\<sigma>\<^sub>,\<^sub>Q\<^sub>] y" == "CONST priTT p x y \<sigma> Q"

definition PriTT :: "('e ttevent) partialorder \<Rightarrow> ('e ttobs) list set \<Rightarrow> ('e ttobs) list set" where
"PriTT p P = {\<rho>|\<rho> s. priTT p \<rho> s [] P \<and> s \<in> P}"

end