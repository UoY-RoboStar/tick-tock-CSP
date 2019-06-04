theory TickTock_PriTT
  imports 
    TickTock_Core
    "Utils.Event_Priority"
begin

definition prirelrefSub3 :: "('e ttevent) partialorder \<Rightarrow> 
                             ('e ttevent) set \<Rightarrow> 
                             ('e ttobs) list \<Rightarrow> 
                             ('e ttobs) list set \<Rightarrow> 
                             ('e ttevent) set" where
"prirelrefSub3 pa S sa Q = 
  (S \<union> {z. (sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z <\<^sup>*pa Tock)} 
     \<union> {z. (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)})"

fun priTT :: "('e ttevent) partialorder \<Rightarrow> 
              ('e ttobs) list \<Rightarrow> 
              ('e ttobs) list \<Rightarrow> 
              ('e ttobs) list \<Rightarrow> 
              ('e ttobs) list set \<Rightarrow> bool" where
"priTT p [] [] s Q = True" |
"priTT p [[R]\<^sub>R] [[S]\<^sub>R] s Q = (R \<subseteq> prirelrefSub3 p S s Q)" |
"priTT p ([R]\<^sub>R # [Tock]\<^sub>E # aa) ([S]\<^sub>R # [Tock]\<^sub>E # zz) s Q =
   ((R \<subseteq> prirelrefSub3 p S s Q) \<and> Tock \<notin> prirelrefSub3 p S s Q \<and> priTT p aa zz (s @ [[S]\<^sub>R,[Tock]\<^sub>E]) Q)" |
"priTT p ([e\<^sub>1]\<^sub>E # aa) ([e\<^sub>2]\<^sub>E # zz) s Q
 = 
 (e\<^sub>1 = e\<^sub>2 \<and> priTT p aa zz (s @ [[e\<^sub>1]\<^sub>E]) Q \<and>
  (maximal(p,e\<^sub>2) 
   \<or> 
  (\<exists>Z. s @ [[Z]\<^sub>R] \<in> Q \<and> e\<^sub>2 \<noteq> Tick \<and> e\<^sub>2 \<notin> prirelrefSub3 p Z s Q)))" |
"priTT p x y s Q = False"

definition PriTT :: "('e ttevent) partialorder \<Rightarrow> ('e ttobs) list set \<Rightarrow> ('e ttobs) list set" where
"PriTT p P = {\<rho>|\<rho> s. priTT p \<rho> s [] P \<and> s \<in> P}"

end
